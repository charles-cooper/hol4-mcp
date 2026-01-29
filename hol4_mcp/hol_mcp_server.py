#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
import hashlib
import json
import os
import signal
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

from fastmcp import FastMCP, Context

from .hol_session import HOLSession, HOLDIR
from .hol_cursor import FileProofCursor


@dataclass
class SessionEntry:
    """Registry entry for a HOL session."""
    session: HOLSession
    started: datetime
    workdir: Path
    cursor: Optional[FileProofCursor] = None
    holmake_env: Optional[dict] = None  # env vars for holmake (auto-captured on success)
    env: Optional[dict] = None  # env vars passed to HOL process


mcp = FastMCP("hol", instructions="""HOL4 theorem prover - proof development workflow:

1. hol_state_at: Check proof state at cursor position (pass file= to auto-init)
2. Edit file directly, then hol_state_at to see new goals
3. Repeat until proof complete
4. holmake: Only at the end to verify the build

Do NOT:
- Call hol_restart after file edits (state_at auto-detects changes)
- Use hol_send for proof navigation (use hol_state_at instead)
""")
_sessions: dict[str, SessionEntry] = {}


def _sigint_handler(signum, frame):
    """Handle SIGINT by interrupting all HOL sessions.
    
    Called when pi sends SIGINT (e.g., user pressed ESC during tool execution).
    Interrupts all running HOL sessions to abort runaway tactics.
    
    Note: Takes a snapshot of sessions to avoid RuntimeError if dict is modified
    concurrently (e.g., session being added/removed when signal arrives).
    """
    # Snapshot to avoid "dictionary changed size during iteration"
    for entry in list(_sessions.values()):
        try:
            entry.session.interrupt()
        except Exception:
            pass  # Best effort - signal handlers must not raise


# Install SIGINT handler (replaces default KeyboardInterrupt behavior)
signal.signal(signal.SIGINT, _sigint_handler)


def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found."""
    entry = _sessions.get(name)
    return entry.session if entry else None


def _get_cursor(name: str) -> Optional[FileProofCursor]:
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
async def hol_start(workdir: str, name: str = "default", env: dict = None) -> str:
    """Start a HOL4 REPL session.

    Idempotent - returns existing session if already running.
    Usually called automatically by hol_state_at (via file= parameter).

    Args:
        workdir: Working directory (should contain Holmakefile for dependencies)
        name: Session identifier (e.g., "main")
        env: Optional environment variables (e.g. {"VFMDIR": "/path/to/vfm"})

    Returns: Session status
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

    # Create session with optional env
    session = HOLSession(str(workdir_path), env=env)

    try:
        result = await session.start()
    except Exception as e:
        return f"ERROR starting HOL: {e}"

    if not session.is_running:
        return f"ERROR: HOL failed to start. Output: {result}"

    # Register session
    _sessions[name] = SessionEntry(session, datetime.now(), workdir_path, env=env)

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
            cursor_str = f"{cs['active_theorem']}" if cs['active_theorem'] else "(none)"
        else:
            cursor_str = "(none)"

        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {status:<8} {cursor_str}")

    return "\n".join(lines)


@mcp.tool()
async def hol_send(session: str, command: str, timeout: int = 5, max_output: int = 4096) -> str:
    """Send raw SML command to HOL session.

    WARNING: Do NOT use for proof navigation - use hol_state_at instead.
    hol_state_at handles file changes, checkpoints, and tactic replay automatically.

    Only use hol_send for:
      - Database queries: DB.match [], ``add _ _``
      - Type checking: type_of ``expr``
      - Term parsing: Term `expr`
      - One-off SML evaluation
      - Debugging session state

    Args:
        session: Session name
        command: SML command to execute
        timeout: Max seconds to wait (default 5, max 600)
        max_output: Max bytes of output to return (default 4096).
                    Shows tail when truncated (errors/results come after echoed input).

    Returns: HOL output (may include errors), truncated if exceeds max_output
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

    # Validate max_output
    if max_output < 1:
        return f"ERROR: max_output must be positive (got {max_output})"

    result = await s.send(command, timeout=timeout)
    
    # Truncate if needed (show tail - errors/results come after echoed input)
    if len(result) > max_output:
        return f"[TRUNCATED: {len(result)} bytes, showing last {max_output}]\n\n{result[-max_output:]}"
    
    return result


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

    # Flush interrupt message by sending dummy command
    # HOL queues "Compilation interrupted" which pollutes next send() otherwise
    await asyncio.sleep(0.1)
    await s.send(";", timeout=1)

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

    Only needed when:
    - HOL state is corrupted (rare)
    - Upstream dependencies changed (edited other .sml files that need Holmake)

    NOT needed for edits to current proof file - state_at auto-detects changes.

    Args:
        session: Session name to restart

    Returns: Same as hol_start (cursor is cleared, use hol_state_at file= to re-init)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found."

    workdir = entry.workdir
    env = entry.env  # Preserve env through restart
    await hol_stop.fn(session)
    return await hol_start.fn(workdir=str(workdir), name=session, env=env)


@mcp.tool()
async def hol_setenv(session: str, env: dict) -> str:
    """Set environment variables for a HOL session.

    These are passed to the HOL process and affect Holmakefile INCLUDES expansion.
    Use before hol_state_at or call hol_restart after to apply.

    Example: hol_setenv("main", {"VFMDIR": "/home/user/verifereum"})

    Args:
        session: Session name
        env: Environment variables to set (merged with existing)

    Returns: Confirmation message
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found. Use hol_start first."

    # Merge with existing env
    if entry.env:
        entry.env.update(env)
    else:
        entry.env = env

    return f"Environment updated for session '{session}': {env}\nUse hol_restart to apply to running session."


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


async def _init_file_cursor(
    file: str,
    session: str = "default",
    workdir: str = None,
    tactic_timeout: float = 5.0,
) -> str:
    """Initialize cursor for a HOL4 script file (internal helper).

    Parses file for theorems and their proofs. Auto-starts HOL session if needed.
    After init, use hol_state_at to navigate to specific positions and see goals.

    Args:
        file: Path to *Script.sml file containing theorems
        session: Session name (default: "default")
        workdir: Working directory for HOL (default: file's parent directory)
        tactic_timeout: Max seconds per tactic (default 5.0). Enforces fast proofs.

    Returns: List of theorems with line numbers and cheat status
    """
    # Validate file first
    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    # Determine target workdir
    target_workdir = Path(workdir).resolve() if workdir else file_path.parent

    # Auto-start or restart session if workdir changed or file content changed
    s = _get_session(session)
    entry = _sessions.get(session)

    if s and s.is_running:
        # Check if workdir differs - need to restart
        if entry and entry.workdir != target_workdir:
            await hol_stop.fn(session)
            s = None
        # Check if file content changed - session has stale definitions
        elif entry and entry.cursor:
            old_cursor = entry.cursor
            if Path(old_cursor.file).resolve() == file_path:
                # Same file - check if content changed
                old_hash = old_cursor._content_hash
                new_content = file_path.read_text()
                new_hash = hashlib.sha256(new_content.encode()).hexdigest()
                if old_hash and new_hash != old_hash:
                    # File changed - restart session to clear stale definitions
                    await hol_stop.fn(session)
                    s = None

    if not s or not s.is_running:
        start_result = await hol_start.fn(workdir=str(target_workdir), name=session)
        if start_result.startswith("ERROR"):
            return start_result
        s = _get_session(session)

    t0 = time.perf_counter()
    
    cursor = FileProofCursor(file_path, s, tactic_timeout=tactic_timeout)
    result = await cursor.init()
    
    init_time = time.perf_counter() - t0

    _sessions[session].cursor = cursor

    if result.get("error"):
        return f"ERROR: {result['error']}"

    # Build status output
    lines = [
        f"File: {file_path}",
        f"Theorems: {len(result['theorems'])} ({len(result['cheats'])} cheats)",
    ]

    if result['cheats']:
        lines.append("")
        lines.append("Cheats to fix:")
        for cheat in result['cheats']:
            lines.append(f"  {cheat['theorem']} (line {cheat['line']})")

    lines.append("")
    lines.append(f"[Init time: {init_time*1000:.0f}ms]")

    return "\n".join(lines)


@mcp.tool()
async def hol_state_at(
    session: str,
    line: int,
    col: int = 1,
    file: str = None,
    workdir: str = None,
) -> str:
    """Get proof state at a file position.

    Replays tactics from theorem start up to (but not including) the tactic at
    the given position, then shows current goals. Auto-enters theorem if needed.

    Args:
        session: Session name
        line: 1-indexed line number (position in the proof)
        col: 1-indexed column number (default 1)
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)

    Returns: Tactic position (N/M), goals at that position, errors if any
    """
    cursor = _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    result = await cursor.state_at(line, col)
    active_theorem = cursor._active_theorem
    thm = cursor._get_theorem(active_theorem) if active_theorem else None

    # Helper to convert tactic index to line:col
    def tactic_to_loc(idx):
        if not thm or not thm.proof_body or idx <= 0:
            return None
        if idx > len(cursor._step_plan):
            idx = len(cursor._step_plan)
        if idx > 0:
            step = cursor._step_plan[idx - 1]
            # Find line and column
            before = thm.proof_body[:step.end]
            line_num = thm.proof_start_line + before.count('\n')
            last_nl = before.rfind('\n')
            col_num = step.end - last_nl if last_nl >= 0 else step.end + 1
            return (line_num, col_num)
        return (thm.proof_start_line, 1)

    lines = []
    
    # Check if "no goals" error is actually success (proof complete)
    is_proof_complete = (
        result.error and 
        "no goals" in result.error.lower() and
        result.tactics_replayed == result.tactics_total and
        not result.goals
    )
    
    # Structural error (not in theorem, etc.) - no goals to show
    if result.error and result.tactics_total == 0:
        lines.append(f"ERROR: {result.error}")
        return "\n".join(lines)
    
    # Show theorem name (useful for hol_check_proof after edits)
    if active_theorem:
        lines.append(f"Theorem: {active_theorem}")
    
    # Show position info - clarify if we couldn't reach requested position
    if result.error and result.tactics_replayed < result.tactic_idx:
        loc = tactic_to_loc(result.tactics_replayed)
        loc_str = f"line {loc[0]} col {loc[1]}" if loc else ""
        lines.append(f"Stuck at {loc_str} (Tactic {result.tactics_replayed}/{result.tactics_total})")
        lines.append(f"\nERROR: {result.error}")
        lines.append("")
        lines.append("=== Goals ===")
    else:
        loc = tactic_to_loc(result.tactic_idx)
        loc_str = f"Line {loc[0]} col {loc[1]}, " if loc else ""
        lines.append(f"{loc_str}Tactic {result.tactic_idx}/{result.tactics_total}")
        # Don't show "no goals" as error when proof is complete
        if result.error and not is_proof_complete:
            lines.append(f"\nERROR: {result.error}")
        lines.append("")
        lines.append("=== Goals ===")

    if result.goals:
        for i, g in enumerate(result.goals):
            if i > 0:
                lines.append("")  # Blank line between goals
            if g.get('asms'):
                for asm in g['asms']:
                    lines.append(f"  {asm}")
                lines.append("  " + "-" * 40)
            lines.append(f"  {g['goal']}")
    elif is_proof_complete:
        lines.append("No goals (proof complete)")
    else:
        lines.append("No goals (proof complete)")

    # Add timing info if available
    if result.timings:
        t = result.timings
        lines.append("")
        lines.append(f"[Timing: total={t.get('total', 0)*1000:.0f}ms, "
                     f"replay={t.get('replay', 0)*1000:.0f}ms, "
                     f"checkpoint={'yes' if t.get('used_checkpoint') else 'no'}]")

    return "\n".join(lines)


@mcp.tool()
async def hol_check_proof(
    session: str,
    theorem: str,
    file: str = None,
    workdir: str = None,
) -> str:
    """Check if a theorem's proof completes after editing.

    Use this after editing a proof to see if it works now. More reliable than
    hol_state_at with line numbers which may be stale after edits.

    Args:
        session: Session name
        theorem: Theorem name to check
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)

    Returns: Whether proof completes, goals at failure point, line numbers
    """
    cursor = _get_cursor(session)

    # Auto-init if file provided
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    # Re-parse file to pick up edits
    cursor._reparse_if_changed()

    # Enter theorem and get step plan
    enter_result = await cursor.enter_theorem(theorem)
    if "error" in enter_result:
        return f"ERROR: {enter_result['error']}"

    thm = cursor._get_theorem(theorem)
    if not thm:
        return f"ERROR: Theorem '{theorem}' not found"

    lines = [
        f"Theorem: {theorem}",
        f"Lines: {thm.start_line}-{thm.proof_end_line - 1}",
        "",
    ]

    if thm.has_cheat:
        lines.append("Status: CHEAT (not verified)")
        return "\n".join(lines)

    # Execute proof
    trace = await cursor.execute_proof_traced(theorem, use_cache=False)
    
    if not trace:
        lines.append("Status: NO TACTICS (trivial or unparseable)")
        return "\n".join(lines)

    # Find failure point and compute line number
    failed_idx = None
    for i, entry in enumerate(trace):
        if entry.error or (i == len(trace) - 1 and entry.goals_after != 0):
            failed_idx = i
            break

    # Compute line number of failing tactic from step plan offset
    def tactic_line(idx):
        if idx is None or idx >= len(cursor._step_plan):
            return thm.proof_start_line  # fallback
        step = cursor._step_plan[idx]
        if thm.proof_body:
            newlines = thm.proof_body[:step.end].count('\n')
            return thm.proof_start_line + newlines
        return thm.proof_start_line

    final = trace[-1]
    total_ms = sum(e.real_ms for e in trace)
    
    if final.error:
        lines.append(f"Status: FAILED at line {tactic_line(failed_idx)} ({total_ms}ms)")
        lines.append(f"Error: {final.error}")
    elif final.goals_after == 0:
        lines.append(f"Status: OK ({total_ms}ms)")
        return "\n".join(lines)
    else:
        lines.append(f"Status: INCOMPLETE at line {tactic_line(len(trace) - 1)} ({total_ms}ms)")

    # Get goals at failure point
    lines.append("")
    goals_output = await cursor.session.send('goals_json();', timeout=10)
    try:
        goals = cursor._parse_goals_json(goals_output)
        lines.append(f"=== Goals ({len(goals)}) ===")
        for i, g in enumerate(goals):
            if i > 0:
                lines.append("")
            if g.get('asms'):
                for asm in g['asms']:
                    lines.append(f"  {asm}")
                lines.append("  " + "-" * 40)
            lines.append(f"  {g['goal']}")
    except:
        lines.append(f"=== Goals ({final.goals_after}) ===")

    return "\n".join(lines)


@mcp.tool()
async def hol_file_status(session: str, file: str = None, workdir: str = None, timing: bool = True) -> str:
    """Get current cursor position and file status.

    Args:
        session: Session name
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        timing: If True, run all proofs and report timing (slower)

    Returns: File info, active theorem, theorems with cheats, completion status
    """
    cursor = _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    status = cursor.status
    total = len(status['theorems'])

    # When timing, we verify proofs by execution; otherwise use static analysis
    if timing:
        # Run all proofs in clean state (efficient batch verification)
        all_traces = await cursor.verify_all_proofs()

        # Process results
        verified = []
        failed = []  # (name, error_msg)
        cheated = []
        timing_lines = []
        total_ms = 0

        for thm in status['theorems']:
            trace = all_traces.get(thm['name'], [])
            if thm['has_cheat']:
                cheated.append(thm['name'])
                timing_lines.append(f"  {thm['name']}: (cheat)")
            elif trace:
                thm_ms = sum(e.real_ms for e in trace)
                total_ms += thm_ms
                error = next((e.error for e in trace if e.error), None)
                # Check proof actually completed (no remaining goals)
                final_goals = trace[-1].goals_after if trace else -1
                if error:
                    failed.append((thm['name'], error))
                    timing_lines.append(f"  {thm['name']}: {thm_ms}ms (ERROR: {error})")
                elif final_goals != 0:
                    failed.append((thm['name'], f"incomplete ({final_goals} goals remain)"))
                    timing_lines.append(f"  {thm['name']}: {thm_ms}ms (INCOMPLETE: {final_goals} goals)")
                else:
                    verified.append(thm['name'])
                    timing_lines.append(f"  {thm['name']}: {thm_ms}ms")
            else:
                timing_lines.append(f"  {thm['name']}: (no tactics)")
                # No tactics = likely just goal statement, count as incomplete
                failed.append((thm['name'], "no tactics"))

        lines = [
            f"File: {status['file']}",
            f"Progress: {len(verified)}/{total} theorems VERIFIED by execution",
            "",
        ]

        if status['active_theorem']:
            lines.append(f"Active theorem: {status['active_theorem']}")
            lines.append(f"Active tactics: {status['active_tactics']}")
        else:
            lines.append("Active theorem: None")

        # Show failures prominently at top
        if failed:
            lines.append("")
            lines.append(f"FAILED ({len(failed)}):")
            for name, err in failed:
                lines.append(f"  {name}: {err}")

        if cheated:
            lines.append("")
            lines.append(f"Cheated ({len(cheated)}): {', '.join(cheated)}")

        lines.append("")
        lines.append(f"Verified: {', '.join(verified) or 'None'}")

        lines.append("")
        lines.append("Proof times:")
        lines.extend(timing_lines)
        lines.append(f"Total: {total_ms}ms")

        # Warn about potential holmake divergence
        if len(verified) == total - len(cheated) and len(cheated) == 0:
            lines.append("")
            lines.append("NOTE: Run 'holmake' to confirm batch build succeeds.")
            lines.append("      Session may have stale theory deps from prior builds.")
    else:
        # Static analysis only (fast but unreliable)
        complete_in_file = [t['name'] for t in status['theorems'] if not t['has_cheat']]

        lines = [
            f"File: {status['file']}",
            f"Progress: {len(complete_in_file)}/{total} theorems (static, unverified)",
            "",
        ]

        if status['active_theorem']:
            lines.append(f"Active theorem: {status['active_theorem']}")
            lines.append(f"Active tactics: {status['active_tactics']}")
        else:
            lines.append("Active theorem: None")

        lines.append("")
        lines.append(f"No cheat keyword: {', '.join(complete_in_file) or 'None'}")

        if status['cheats']:
            lines.append("")
            lines.append(f"Has cheat keyword ({len(status['cheats'])}):")
            for c in status['cheats']:
                marker = " <--" if c['theorem'] == status['active_theorem'] else ""
                lines.append(f"  {c['theorem']} (line {c['line']}){marker}")

    return "\n".join(lines)


# =============================================================================
# Proof Timing Trace Tools
# =============================================================================


@mcp.tool()
async def hol_trace_proof(
    session: str,
    theorem: str,
    file: str = None,
    workdir: str = None,
) -> str:
    """Execute a proof and return full timing trace.

    Executes all tactics for the given theorem and records timing
    for each step.

    Args:
        session: Session name
        theorem: Theorem name to trace
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)

    Returns: Full trace with timing for each tactic
    """
    cursor = _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    trace = await cursor.execute_proof_traced(theorem)

    if not trace:
        return f"No trace data. Theorem '{theorem}' may not exist or has no tactics."

    lines = [f"Proof trace for {theorem}: {len(trace)} steps", ""]

    total_real = 0
    has_error = False
    for i, entry in enumerate(trace, 1):
        total_real += entry.real_ms
        lines.append(f"Step {i}: {entry.cmd[:60]}{'...' if len(entry.cmd) > 60 else ''}")
        if entry.error:
            lines.append(f"  ERROR: {entry.error}")
            has_error = True
        else:
            lines.append(f"  Real: {entry.real_ms}ms, User: {entry.usr_ms}ms, Sys: {entry.sys_ms}ms")
            lines.append(f"  Goals: {entry.goals_before} -> {entry.goals_after}")
        lines.append("")

    lines.append(f"Total real time: {total_real}ms")
    if has_error:
        lines.append("WARNING: Trace incomplete due to error")

    return "\n".join(lines)


def _install_pi_extension():
    """Install the pi extension to ~/.pi/agent/extensions/."""
    import shutil
    
    # Find the extension file bundled with the package
    ext_source = Path(__file__).parent / "pi_extension" / "hol4-mcp.ts"
    if not ext_source.exists():
        print(f"Error: Extension file not found at {ext_source}", file=sys.stderr)
        sys.exit(1)
    
    # Target directory
    ext_dir = Path.home() / ".pi" / "agent" / "extensions"
    ext_dir.mkdir(parents=True, exist_ok=True)
    
    ext_target = ext_dir / "hol4-mcp.ts"
    shutil.copy2(ext_source, ext_target)
    print(f"Installed pi extension to {ext_target}")


def main():
    """CLI entry point for HOL4 MCP server."""
    import argparse
    import logging

    parser = argparse.ArgumentParser(description="HOL4 MCP Server and Tools")
    subparsers = parser.add_subparsers(dest="command")

    # install-pi subcommand
    subparsers.add_parser("install-pi", help="Install pi extension to ~/.pi/agent/extensions/")

    # serve subcommand (default behavior)
    serve_parser = subparsers.add_parser("serve", help="Run the MCP server (default)")
    serve_parser.add_argument(
        "--transport",
        choices=["stdio", "http", "sse"],
        default="stdio",
        help="Transport protocol (default: stdio)",
    )
    serve_parser.add_argument("--port", type=int, default=8000, help="Port for HTTP/SSE (default: 8000)")
    serve_parser.add_argument("--host", default="127.0.0.1", help="Host for HTTP/SSE (default: 127.0.0.1)")
    serve_parser.add_argument("-v", "--verbose", action="store_true", help="Enable debug logging")

    # Also allow serve options at top level for backwards compat
    parser.add_argument("--transport", choices=["stdio", "http", "sse"], default="stdio", help=argparse.SUPPRESS)
    parser.add_argument("--port", type=int, default=8000, help=argparse.SUPPRESS)
    parser.add_argument("--host", default="127.0.0.1", help=argparse.SUPPRESS)
    parser.add_argument("-v", "--verbose", action="store_true", help=argparse.SUPPRESS)

    args = parser.parse_args()

    if args.command == "install-pi":
        _install_pi_extension()
        return

    # Default to serve behavior
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
