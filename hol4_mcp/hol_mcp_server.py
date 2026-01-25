#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
import json
import os
import signal
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

from fastmcp import FastMCP, Context

from .hol_session import HOLSession, HOLDIR
from .hol_cursor import ProofCursor
from .hol_file_parser import parse_file


@dataclass
class SessionEntry:
    """Registry entry for a HOL session."""
    session: HOLSession
    started: datetime
    workdir: Path
    cursor: Optional[ProofCursor] = None
    holmake_env: Optional[dict] = None  # env vars for holmake (auto-captured on success)


mcp = FastMCP("hol", instructions="""HOL4 theorem prover.
holmake: build. hol_start/hol_send: interactive. hol_cursor_*: file-based proofs.""")
_sessions: dict[str, SessionEntry] = {}


def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found."""
    entry = _sessions.get(name)
    return entry.session if entry else None


def _get_cursor(name: str) -> Optional[ProofCursor]:
    """Get cursor from registry, or None if not found."""
    entry = _sessions.get(name)
    return entry.cursor if entry else None


def _session_age(name: str) -> str:
    """Get human-readable session age."""
    entry = _sessions.get(name)
    if not entry:
        return "unknown"
    started = entry.started
    delta = datetime.now() - started
    secs = int(delta.total_seconds())
    if secs < 60:
        return f"{secs}s"
    elif secs < 3600:
        return f"{secs // 60}m"
    else:
        return f"{secs / 3600:.1f}h"


@mcp.tool()
async def hol_start(workdir: str, name: str = "default") -> str:
    """Start HOL session (idempotent - returns existing if running).

    Args:
        workdir: Working directory for HOL (where Holmakefile is)
        name: Session identifier (use simple names like 'main')

    Returns: Session status and current proof state
    """
    # If session exists and is running, return its state
    if name in _sessions:
        session = _sessions[name].session
        if session.is_running:
            goals = await session.send("top_goals();", timeout=10)
            return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"
        # Dead session - clean up
        del _sessions[name]

    # Validate workdir
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Working directory does not exist: {workdir}"

    # Create session
    session = HOLSession(str(workdir_path))

    try:
        result = await session.start()
    except Exception as e:
        return f"ERROR starting HOL: {e}"

    if not session.is_running:
        return f"ERROR: HOL failed to start. Output: {result}"

    # Register session
    _sessions[name] = SessionEntry(session, datetime.now(), workdir_path)

    return f"Session '{name}' started. {result}\nWorkdir: {workdir_path}"


@mcp.tool()
async def hol_sessions() -> str:
    """List all active HOL sessions with their workdir, age, status, cursor."""
    if not _sessions:
        return "No active sessions."

    lines = ["SESSION      WORKDIR                                    AGE     STATUS   CURSOR"]
    lines.append("-" * 95)

    for name, entry in _sessions.items():
        status = "running" if entry.session.is_running else "dead"
        age = _session_age(name)
        workdir_str = str(entry.workdir)
        if len(workdir_str) > 40:
            workdir_str = "..." + workdir_str[-37:]

        # Cursor info
        if entry.cursor:
            cs = entry.cursor.status
            cursor_str = f"{cs['current']} ({cs['position']})" if cs['current'] else "(none)"
        else:
            cursor_str = "(none)"

        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {status:<8} {cursor_str}")

    return "\n".join(lines)


@mcp.tool()
async def hol_send(session: str, command: str, timeout: int = 5) -> str:
    """Send SML to HOL.

    NEVER use g/e (goalstack). ALWAYS use gt/etq (goaltree):
      gt `goal`;         (* start proof *)
      etq "tactic";      (* apply tactic, records for p() *)
      p();               (* extract proof script *)
      backup(); drop();  (* undo / abandon *)

    Args: session, command, timeout (default 5, max 600)
    """
    s = _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    # Validate timeout
    if timeout < 1:
        timeout = 1
    elif timeout > 600:
        timeout = 600

    return await s.send(command, timeout=timeout)


@mcp.tool()
async def hol_interrupt(session: str) -> str:
    """Send SIGINT to abort runaway tactic.

    Args:
        session: Session name from hol_start

    Returns: Confirmation message
    """
    s = _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died."

    s.interrupt()

    # Try to read any output
    await asyncio.sleep(0.5)

    return f"Sent SIGINT to session '{session}'. The tactic should be interrupted."


@mcp.tool()
async def hol_stop(session: str) -> str:
    """Terminate HOL session.

    Args:
        session: Session name from hol_start

    Returns: Confirmation message
    """
    entry = _sessions.pop(session, None)
    if entry:
        await entry.session.stop()
        return f"Session '{session}' stopped."
    return f"Session '{session}' not found."


@mcp.tool()
async def hol_restart(session: str) -> str:
    """Restart HOL session (stop + start, preserves workdir).

    Use when HOL state is corrupted or you need to reload theories after file changes.

    Args:
        session: Session name to restart

    Returns: Same as hol_start (session info + proof state)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found."

    workdir = entry.workdir
    await hol_stop.fn(session)
    return await hol_start.fn(workdir=str(workdir), name=session)


async def _kill_process_group(proc):
    """Kill process group: SIGTERM, wait, SIGKILL if needed.

    Must kill even if parent exited - children (buildheap) may still be alive.
    """
    if proc is None:
        return

    pgid = proc.pid

    # Send SIGTERM to the whole process group
    try:
        os.killpg(pgid, signal.SIGTERM)
    except OSError:
        return  # Process group doesn't exist

    # Wait for processes to die gracefully (up to 1s)
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=1.0)
        except (asyncio.TimeoutError, asyncio.CancelledError):
            pass
    else:
        # Parent already exited, give children time to die from SIGTERM
        try:
            await asyncio.sleep(1.0)
        except asyncio.CancelledError:
            pass  # Still need to SIGKILL

    # SIGKILL anything remaining in the group
    try:
        os.killpg(pgid, signal.SIGKILL)
    except OSError:
        pass  # Already gone

    # Reap parent if needed
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=0.5)
        except:
            pass


# Progress reporting interval for long builds (resets MCP client timeout)
_PROGRESS_INTERVAL = 10  # seconds


@mcp.tool()
async def holmake(workdir: str, target: str = None, env: dict = None, log_limit: int = 1024, timeout: int = 90, ctx: Context = None) -> str:
    """Run Holmake --qof in directory.

    Args:
        workdir: Directory containing Holmakefile
        target: Optional specific target to build
        env: Optional environment variables (e.g. {"MY_VAR": "/some/path"})
        log_limit: Max bytes per log file to include on failure (default 1024)
        timeout: Max seconds to wait (default 90, max 1800)

    Returns: Holmake output (stdout + stderr). On failure, includes recent build logs.

    Note: For builds > 60s, progress notifications are sent every 10s to prevent
    MCP client timeout. Configure tool_timeout_sec in ~/.codex/config.toml if needed.
    """
    # Validate timeout
    timeout = max(1, min(timeout, 1800))
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Directory does not exist: {workdir}"

    holmake_bin = HOLDIR / "bin" / "Holmake"
    if not holmake_bin.exists():
        return f"ERROR: Holmake not found at {holmake_bin}"

    logs_dir = workdir_path / ".hol" / "logs"

    # Snapshot existing log mtimes before build
    pre_logs = {}
    if logs_dir.exists():
        for log_file in logs_dir.iterdir():
            if log_file.is_file():
                pre_logs[log_file.name] = log_file.stat().st_mtime

    cmd = [str(holmake_bin), "--qof"]
    if target:
        cmd.append(target)

    # Build environment
    proc_env = os.environ.copy()
    if env:
        proc_env.update(env)

    proc = None
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            cwd=workdir_path,
            env=proc_env,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            start_new_session=True,
        )

        # Poll with progress reporting to prevent MCP client timeout
        start_time = time.time()
        stdout_chunks = []
        timed_out = False

        while True:
            elapsed = time.time() - start_time
            if elapsed >= timeout:
                timed_out = True
                break

            # Report progress to reset client timeout (MCP resetTimeoutOnProgress)
            if ctx:
                try:
                    await ctx.report_progress(
                        progress=elapsed,
                        total=float(timeout),
                        message=f"Building... {int(elapsed)}s / {timeout}s"
                    )
                except Exception:
                    pass  # Don't fail build if progress reporting fails

            # Wait for output or timeout after interval
            try:
                chunk = await asyncio.wait_for(
                    proc.stdout.read(4096),
                    timeout=min(_PROGRESS_INTERVAL, timeout - elapsed)
                )
                if chunk:
                    stdout_chunks.append(chunk)
                else:
                    # EOF - wait for process to finish
                    try:
                        await asyncio.wait_for(proc.wait(), timeout=5)
                    except asyncio.TimeoutError:
                        pass
                    break
            except asyncio.TimeoutError:
                # Check if process finished
                if proc.returncode is not None:
                    break
                continue  # Keep polling

        if timed_out:
            return f"ERROR: Build timed out after {timeout}s."

        output = b''.join(stdout_chunks).decode("utf-8", errors="replace")

        if proc.returncode == 0:
            result = f"Build succeeded.\n\n{output}"
            if env:
                # Store env in matching session entries for auto-holmake at startup
                for entry in _sessions.values():
                    if entry.workdir == workdir_path:
                        entry.holmake_env = env
                # Include env in output for caller to capture if needed
                result += f"\nHOLMAKE_ENV: {json.dumps(env)}"
            return result

        # Build failed - append relevant logs
        result = f"Build failed (exit code {proc.returncode}).\n\n{output}"

        if logs_dir.exists():
            # Find logs modified during build
            modified = []
            for log_file in logs_dir.iterdir():
                if not log_file.is_file():
                    continue
                mtime = log_file.stat().st_mtime
                if log_file.name not in pre_logs or mtime > pre_logs[log_file.name]:
                    modified.append((log_file, mtime))

            if modified:
                # Sort by mtime descending (most recent first)
                modified.sort(key=lambda x: -x[1])
                result += "\n\n=== Build Logs ===\n"
                for log_file, _ in modified[:3]:
                    content = log_file.read_text(errors="replace")
                    if len(content) > log_limit:
                        content = f"...(truncated, showing last {log_limit} bytes)...\n" + content[-log_limit:]
                    result += f"\n--- {log_file.name} ---\n{content}\n"

        return result

    except Exception as e:
        return f"ERROR: {e}"
    finally:
        await _kill_process_group(proc)


@mcp.tool()
async def hol_log(workdir: str, theory: str, limit: int = 1024) -> str:
    """Read build log for a specific theory.

    Use after holmake to inspect warnings or errors in detail.

    Args:
        workdir: Directory containing .hol/logs/
        theory: Theory name (e.g., "fooTheory")
        limit: Max bytes to return (default 1024, 0 for unlimited)

    Returns: Log file contents (tail if truncated)
    """
    workdir_path = Path(workdir).resolve()
    log_file = workdir_path / ".hol" / "logs" / theory

    if not log_file.exists():
        # Try without "Theory" suffix
        log_file = workdir_path / ".hol" / "logs" / f"{theory}Theory"
        if not log_file.exists():
            available = []
            logs_dir = workdir_path / ".hol" / "logs"
            if logs_dir.exists():
                available = [f.name for f in logs_dir.iterdir() if f.is_file()]
            if available:
                return f"Log not found: {theory}\nAvailable: {', '.join(sorted(available))}"
            return f"Log not found: {theory}\nNo logs in {logs_dir}"

    content = log_file.read_text(errors="replace")
    if limit > 0 and len(content) > limit:
        return f"...(truncated, showing last {limit} bytes)...\n{content[-limit:]}"
    return content


@mcp.tool()
async def hol_logs(workdir: str) -> str:
    """List available build logs.

    Args:
        workdir: Directory containing .hol/logs/

    Returns: List of log files with sizes and modification times
    """
    workdir_path = Path(workdir).resolve()
    logs_dir = workdir_path / ".hol" / "logs"

    if not logs_dir.exists():
        return f"No logs directory: {logs_dir}"

    logs = []
    for log_file in sorted(logs_dir.iterdir()):
        if log_file.is_file():
            stat = log_file.stat()
            size = stat.st_size
            mtime = datetime.fromtimestamp(stat.st_mtime).strftime("%H:%M:%S")
            logs.append(f"  {log_file.name}: {size} bytes, modified {mtime}")

    if not logs:
        return "No log files found."
    return "Build logs:\n" + "\n".join(logs)


# =============================================================================
# Cursor Tools (for multi-theorem files)
# =============================================================================


@mcp.tool()
async def hol_cursor_init(file: str, session: str = "default", workdir: str = None, start_at: str = None) -> str:
    """Initialize cursor and start proving a theorem.

    Parses file, finds theorems with cheats, loads HOL context, and enters
    goaltree mode for the specified theorem (or first cheat if not specified).

    Auto-starts HOL session if needed.

    Args:
        file: Path to .sml file containing theorems
        session: Session name (default: "default")
        workdir: Working directory for HOL (default: file's parent directory)
        start_at: Theorem name to start at (default: first cheat)

    Returns: Status showing current position, theorems found, and current goals
    """
    # Validate file first
    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    # Auto-start session if needed
    s = _get_session(session)
    if not s or not s.is_running:
        wd = workdir or str(file_path.parent)
        start_result = await hol_start.fn(workdir=wd, name=session)
        if start_result.startswith("ERROR"):
            return start_result
        s = _get_session(session)

    cursor = ProofCursor(file_path, s)
    result = await cursor.initialize()

    _sessions[session].cursor = cursor

    # Jump to specific theorem if requested
    if start_at:
        thm = cursor.goto(start_at)
        if not thm:
            available = [t.name for t in cursor.theorems if t.has_cheat]
            return f"ERROR: Theorem '{start_at}' not found.\nAvailable cheats: {', '.join(available)}"
        # Load context up to target theorem
        await cursor.load_context_to(thm.start_line)
        result = f"Positioned at {thm.name} (line {thm.cheat_line or thm.proof_start_line})"

    # Build status
    status = cursor.status
    lines = [
        result,
        "",
        f"File: {status['file']}",
        f"Theorems: {status['position']}",
        f"Cheated theorems: {len(status['cheated_theorems'])}",
    ]

    if status['current']:
        lines.append(f"Current: {status['current']} (line {status['current_line']})")

        # Enter goaltree for current theorem
        start_result = await cursor.start_current()
        goals = await s.send("top_goals();", timeout=10)
        lines.append("")
        lines.append(f"=== Proving {status['current']} ===")
        lines.append(start_result)
        lines.append("")
        lines.append("=== Current goals ===")
        lines.append(goals)

    return "\n".join(lines)


@mcp.tool()
async def hol_cursor_status(session: str) -> str:
    """Get current cursor position and status.

    Args:
        session: Session name

    Returns: Progress, current theorem, completed proofs (ground truth from file), remaining cheats
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    # Reparse for ground truth (file may have been edited)
    cursor.theorems = parse_file(cursor.file)

    status = cursor.status
    # Ground truth: theorems without cheats in file (not just session-completed)
    complete_in_file = [t.name for t in cursor.theorems if not t.has_cheat]
    total = len(cursor.theorems)

    lines = [
        f"File: {status['file']}",
        f"Progress: {len(complete_in_file)}/{total} theorems complete",
        f"Current: {status['current']} (line {status['current_line']})" if status['current'] else "Current: None",
        f"Completed: {', '.join(complete_in_file) or 'None'}",
        "",
        f"Cheated theorems ({len(status['cheated_theorems'])}):",
    ]
    for c in status['cheated_theorems']:
        marker = " <--" if c['name'] == status['current'] else ""
        lines.append(f"  {c['name']} (line {c['line']}){marker}")
    return "\n".join(lines)


@mcp.tool()
async def hol_cursor_goto(session: str, theorem_name: str) -> str:
    """Jump to specific theorem by name and enter goaltree.

    Use to skip ahead or go back to a different cheat.
    Drops current proof state before jumping.

    Args:
        session: Session name
        theorem_name: Name of theorem to jump to

    Returns: Theorem info and current goals
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    s = _get_session(session)
    if not s or not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    # Drop current proof state
    await s.send("drop();", timeout=5)

    # Reparse file for fresh line numbers, then jump to theorem
    cursor.theorems = parse_file(cursor.file)
    thm = cursor.goto(theorem_name)
    if not thm:
        available = [t.name for t in cursor.theorems if t.has_cheat]
        return f"ERROR: Theorem '{theorem_name}' not found.\nAvailable cheats: {', '.join(available)}"

    if not thm.has_cheat:
        return f"WARNING: {theorem_name} has no cheat (already proved)."

    # Load context up to target theorem
    await cursor.load_context_to(thm.start_line)

    # Enter goaltree
    result = await cursor.start_current()
    goals = await s.send("top_goals();", timeout=10)

    return f"Jumped to {theorem_name} (line {thm.cheat_line or thm.proof_start_line})\n{result}\n\n=== Current goals ===\n{goals}"


@mcp.tool()
async def hol_cursor_reenter(session: str) -> str:
    """Re-enter goaltree for current theorem.

    Reparses the file to handle edits (e.g., after splicing a completed proof),
    then re-enters goaltree. If the current theorem was completed (no longer
    has cheat), advances to the next theorem with a cheat.

    This tool serves two purposes:
    1. After hol_cursor_complete + edit: loads completed theorem into HOL, advances
    2. Retry: re-enter same theorem from scratch after exploring dead-end tactics

    Args:
        session: Session name

    Returns: Confirmation and current goal state
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    s = _get_session(session)
    if not s or not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    # Reparse file to get fresh line numbers (handles edits)
    current_name = cursor.current().name if cursor.current() else None
    cursor.theorems = parse_file(cursor.file)

    # Compute cheat_line for all theorems
    await cursor._compute_cheat_lines()

    # Re-locate by name (position may have shifted), then advance if completed
    if current_name:
        cursor.goto(current_name)
    current = cursor.current()
    if not current or not current.has_cheat:
        if not cursor.next_cheat():
            return "All cheats complete!"

    result = await cursor.start_current()
    goals = await s.send("top_goals();", timeout=10)

    return f"{result}\n\n=== Current goals ===\n{goals}"


@mcp.tool()
async def hol_cursor_complete(session: str) -> str:
    """Extract completed proof, drop goal, advance to next cheat.

    Call when proof is done (no goals remaining). Returns the proof script
    for you to splice into the file yourself.

    Does NOT modify the filesystem - you are responsible for editing the file
    to replace the cheat() with the returned proof.

    Args:
        session: Session name

    Returns: The proof script, theorem name, and next cheat info.
             After splicing the proof, use hol_cursor_reenter to set up the next theorem.
    """
    cursor = _get_cursor(session)
    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Use hol_cursor_init() first."

    s = _get_session(session)
    if not s or not s.is_running:
        return f"ERROR: Session '{session}' is not running."

    result = await cursor.extract_proof()

    # Handle error case
    if "error" in result:
        return f"ERROR: {result['error']}"

    # Get remaining cheats (excluding the one just completed)
    remaining = [t for t in cursor.theorems if t.has_cheat and t.name != result['theorem']]

    # Format successful result
    lines = [
        f"Completed: {result['theorem']}",
        "",
        "=== Proof script (splice this into file) ===",
        result['proof'],
        "",
    ]

    if remaining:
        lines.append(f"Remaining cheated theorems ({len(remaining)}):")
        for t in remaining:
            lines.append(f"  {t.name} (line {t.cheat_line or t.proof_start_line})")
        lines.extend([
            "",
            "Next steps:",
            "1. Edit the file to replace the cheat() with the proof above",
            "2. Run holmake to verify the proof compiles",
            "3. Call hol_cursor_reenter to load completed theorem and continue",
        ])
    else:
        lines.append("All cheats complete! Edit the file to splice in the final proof, then run holmake to verify.")

    return "\n".join(lines)


def main():
    """Entry point for the HOL4 MCP server."""
    import argparse
    import logging
    import sys

    parser = argparse.ArgumentParser(description="HOL4 MCP Server")
    parser.add_argument(
        "--transport",
        choices=["stdio", "http", "sse"],
        default="stdio",
        help="Transport protocol (default: stdio)",
    )
    parser.add_argument("--port", type=int, default=8000, help="Port for HTTP/SSE (default: 8000)")
    parser.add_argument("--host", default="127.0.0.1", help="Host for HTTP/SSE (default: 127.0.0.1)")
    parser.add_argument("-v", "--verbose", action="store_true", help="Enable debug logging")
    args = parser.parse_args()

    if args.verbose:
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(asctime)s %(levelname)s %(name)s: %(message)s",
            stream=sys.stderr,
        )
        logging.getLogger("mcp").setLevel(logging.DEBUG)

    if args.transport == "stdio":
        mcp.run()
    else:
        print(f"HOL MCP server starting on {args.host}:{args.port} ({args.transport})", file=sys.stderr)
        mcp.run(transport=args.transport, host=args.host, port=args.port)


if __name__ == "__main__":
    main()
