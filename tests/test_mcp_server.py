"""Test the HOL MCP server tools."""

import asyncio
import os
import shutil
import signal

import pytest
from pathlib import Path

from hol4_mcp.hol_mcp_server import (
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_sessions as _hol_sessions,
    hol_stop as _hol_stop,
    hol_log as _hol_log,
    hol_logs as _hol_logs,
    holmake as _holmake,
    hol_file_init as _hol_file_init,
    hol_state_at as _hol_state_at,
    hol_file_status as _hol_file_status,
    _kill_process_group,
)

# Unwrap FunctionTool to get actual functions
hol_start = _hol_start.fn
hol_send = _hol_send.fn
hol_sessions = _hol_sessions.fn
hol_stop = _hol_stop.fn
hol_log = _hol_log.fn
hol_logs = _hol_logs.fn
holmake = _holmake.fn
hol_file_init = _hol_file_init.fn
hol_state_at = _hol_state_at.fn
hol_file_status = _hol_file_status.fn

FIXTURES_DIR = Path(__file__).parent / "fixtures"


@pytest.fixture
def workdir():
    return str(FIXTURES_DIR)


@pytest.fixture
def isolated_workdir(tmp_path):
    """Copy fixtures to isolated temp directory for tests that modify state."""
    # Copy all fixture files to temp dir
    for f in FIXTURES_DIR.iterdir():
        if f.is_file():
            shutil.copy(f, tmp_path / f.name)
    return str(tmp_path)


async def test_session_lifecycle(workdir):
    """Test basic session start/list/send/stop."""
    result = await hol_start(workdir=workdir, name="test")
    assert "Session 'test' started" in result
    assert "HOL started (PID" in result

    try:
        result = await hol_sessions()
        assert "test" in result
        assert "running" in result

        result = await hol_send(session="test", command="1 + 1;")
        assert "val it = 2" in result
    finally:
        result = await hol_stop(session="test")
        assert "Session 'test' stopped" in result


async def test_goaltree_mode(workdir):
    """Test goaltree mode proving."""
    await hol_stop(session="gt_test")
    await hol_start(workdir=workdir, name="gt_test")

    try:
        result = await hol_send(session="gt_test", command="gt `1 + 1 = 2`;")
        assert "Proof manager status: 1 proof" in result
        assert "Initial goal:" in result

        result = await hol_send(session="gt_test", command='etq "EVAL_TAC";')
        assert "OK" in result

        # Check proof state via hol_send
        result = await hol_send(session="gt_test", command="top_goals();")
        assert "val it = []: goal list" in result  # No remaining goals
    finally:
        await hol_stop(session="gt_test")


async def test_p_output_multiline_integration(workdir):
    """Integration test: parse_p_output handles multi-line val it format from real HOL."""
    from hol4_mcp.hol_file_parser import parse_p_output

    await hol_stop(session="p_multi_test")
    await hol_start(workdir=workdir, name="p_multi_test")

    try:
        # Create a proof with multiple tactics to produce multi-line p() output
        await hol_send(session="p_multi_test", command="gt `A /\\ B ==> B /\\ A`;")
        await hol_send(session="p_multi_test", command='etq "strip_tac";')
        await hol_send(session="p_multi_test", command='etq "conj_tac";')
        await hol_send(session="p_multi_test", command='etq "first_assum ACCEPT_TAC";')
        await hol_send(session="p_multi_test", command='etq "first_assum ACCEPT_TAC";')

        # p() on complete proof can produce multi-line "val it = ..." format
        result = await hol_send(session="p_multi_test", command="p();")

        # Verify we got multi-line format with ": proof" type annotation
        assert "\n" in result.strip(), f"Expected multi-line output, got: {result!r}"
        assert ": proof" in result, f"Expected complete proof format, got: {result!r}"

        # Check for multi-line val it format: "val it =" on its own line or
        # single-line format with content after "val it = "
        has_multiline_val_it = "val it =\n" in result or "val it = \n" in result
        has_singleline_val_it = "val it = " in result and ": proof" in result

        # Either format is valid - the key is parse_p_output handles it
        assert has_multiline_val_it or has_singleline_val_it, (
            f"Expected val it format, got: {result!r}"
        )

        # Verify parse_p_output handles whatever format HOL produced
        parsed = parse_p_output(result)
        assert parsed is not None, f"parse_p_output failed on: {result!r}"
        assert "strip_tac" in parsed
        assert "conj_tac" in parsed
        assert ": proof" not in parsed  # Type annotation stripped
    finally:
        await hol_stop(session="p_multi_test")


async def test_db_search(workdir):
    """Test theorem database search."""
    await hol_stop(session="db_test")
    await hol_start(workdir=workdir, name="db_test")

    try:
        result = await hol_send(session="db_test", command='DB.find "ADD";', timeout=15)
        assert "ADD" in result
        assert "⊢" in result  # Theorem statements contain turnstile
    finally:
        await hol_stop(session="db_test")


async def test_build_and_logs(isolated_workdir):
    """Test holmake generates logs, then test hol_logs/hol_log."""
    result = await holmake(workdir=isolated_workdir, target="testTheory")
    assert "Build succeeded" in result
    assert "testTheory" in result

    result = await hol_logs(workdir=isolated_workdir)
    assert "Build logs:" in result
    assert "testTheory" in result

    result = await hol_log(workdir=isolated_workdir, theory="testTheory", limit=500)
    assert 'theory "test"' in result.lower()

    result = await hol_log(workdir=isolated_workdir, theory="test", limit=500)
    assert 'theory "test"' in result.lower()


async def test_build_failure_includes_logs(isolated_workdir):
    """Test that build failure includes log output."""
    result = await holmake(workdir=isolated_workdir, target="failTheory")
    assert "Build failed" in result
    assert "=== Build Logs ===" in result
    assert "failTheory" in result


async def test_log_nonexistent(workdir):
    """Test hol_log for non-existent theory."""
    result = await hol_log(workdir=workdir, theory="nonexistent")
    assert "Log not found: nonexistent" in result
    assert "Available:" in result


async def test_holmake_env_in_output(isolated_workdir):
    """Test that holmake returns env in output on success."""
    import json

    # Build with env - should include in output
    test_env = {"TEST_VAR": "test_value"}
    result = await holmake(workdir=isolated_workdir, target="testTheory", env=test_env)
    assert "Build succeeded" in result
    assert "HOLMAKE_ENV: " in result

    # Parse env from output
    import re
    match = re.search(r"HOLMAKE_ENV: (\{.*\})", result)
    assert match is not None
    parsed_env = json.loads(match.group(1))
    assert parsed_env == test_env

    # Build without env - no HOLMAKE_ENV line
    result = await holmake(workdir=isolated_workdir, target="testTheory", env=None)
    assert "Build succeeded" in result
    assert "HOLMAKE_ENV: " not in result


# =============================================================================
# File Cursor MCP Tool Tests
# =============================================================================


async def test_file_init_lists_theorems(tmp_path):
    """Test hol_file_init parses file and lists theorems."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        result = await hol_file_init(file=str(test_file), session="file_init_test")
        assert "Theorems:" in result
        assert "cheats" in result.lower()
        assert "Verified:" in result
        # Should list cheats to fix
        assert "needs_proof" in result
        assert "partial_proof" in result
    finally:
        await hol_stop(session="file_init_test")


async def test_file_status_shows_cheats(tmp_path):
    """Test hol_file_status lists cheats and active theorem."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="status_test")
        result = await hol_file_status(session="status_test")

        # Should show file info
        assert "File:" in result
        assert "Progress:" in result
        # Should list cheats
        assert "needs_proof" in result
        assert "partial_proof" in result
    finally:
        await hol_stop(session="status_test")


async def test_file_init_restarts_on_workdir_change(tmp_path):
    """Test hol_file_init restarts session when workdir changes.

    Regression test for BUG_workdir_mismatch: when hol_file_init was called
    with a different workdir, the session kept using the old workdir.
    """
    # Create two directories with test files
    dir_a = tmp_path / "dirA"
    dir_b = tmp_path / "dirB"
    dir_a.mkdir()
    dir_b.mkdir()

    file_a = dir_a / "testScript.sml"
    file_b = dir_b / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", file_a)
    shutil.copy(FIXTURES_DIR / "testScript.sml", file_b)

    try:
        # Start session in dir_a
        result = await hol_file_init(file=str(file_a), session="workdir_test")
        assert "Theorems:" in result

        # Check workdir via sessions list
        sessions = await hol_sessions()
        assert "dirA" in sessions

        # Now init for file in dir_b - should restart session
        result = await hol_file_init(file=str(file_b), session="workdir_test", workdir=str(dir_b))
        assert "Theorems:" in result

        # Check workdir changed
        sessions = await hol_sessions()
        assert "dirB" in sessions
        # Old workdir should not be present (session was restarted)
        assert "dirA" not in sessions or "workdir_test" not in sessions.split("dirA")[0]
    finally:
        await hol_stop(session="workdir_test")


async def test_state_at_returns_goals(tmp_path):
    """Test hol_state_at returns goals when called on a line inside a theorem."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="state_at_test")

        # needs_proof theorem starts at line 18, Proof at line 20, cheat at line 21
        # Get state at line 21 (inside the proof, at the cheat line)
        result = await hol_state_at(session="state_at_test", line=21, col=1)

        # Should show tactic info (even if 0/N since cheat is the only tactic)
        assert "Tactic" in result
        # Should show goals (proof is not complete since cheat doesn't prove anything)
        assert "Goals" in result or "goals" in result.lower()
        # Should NOT have error about position outside theorem
        assert "not within any theorem" not in result
    finally:
        await hol_stop(session="state_at_test")


async def test_state_at_outside_theorem(tmp_path):
    """Test hol_state_at returns error when called outside any theorem."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="outside_test")

        # Line 8 is 'val _ = new_theory "test";' - outside any theorem
        result = await hol_state_at(session="outside_test", line=8, col=1)

        # Should return an error about position not being in a theorem
        assert "ERROR" in result
        assert "not within any theorem" in result
    finally:
        await hol_stop(session="outside_test")


async def test_state_at_qed_line(tmp_path):
    """Test hol_state_at on QED line shows final state (proof complete)."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="qed_test")

        # add_zero theorem: Proof at line 14, simp[] at line 14, QED at line 15
        # Querying QED line should show final state with all tactics replayed
        result = await hol_state_at(session="qed_test", line=15, col=1)

        # Should show all tactics replayed
        assert "Tactic" in result
        # Should show proof complete (no goals)
        assert "proof complete" in result.lower()
        # Should NOT have error about position
        assert "ERROR" not in result
    finally:
        await hol_stop(session="qed_test")


async def test_state_at_after_qed_line(tmp_path):
    """Test hol_state_at after QED line returns error."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="after_qed_test")

        # add_zero theorem ends at QED on line 15
        # Line 16 is blank, line 17 starts next theorem
        # Querying line 16 should give an error (outside theorem bounds)
        result = await hol_state_at(session="after_qed_test", line=16, col=1)

        # Should have error about position not in theorem
        assert "ERROR" in result or "not within any theorem" in result
        # Should NOT say "proof complete" since this is an error case
        assert "proof complete" not in result.lower() or "ERROR" in result
    finally:
        await hol_stop(session="after_qed_test")


async def test_state_at_auto_init(tmp_path):
    """Test hol_state_at with file parameter auto-calls hol_file_init."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    session_name = "auto_init_test"
    await hol_stop(session=session_name)  # Ensure clean state

    try:
        # Call hol_state_at with file parameter - should auto-init
        result = await hol_state_at(
            session=session_name, line=21, col=1, file=str(test_file)
        )

        # Should work without explicit hol_file_init
        assert "Tactic" in result
        assert "ERROR: No cursor" not in result
    finally:
        await hol_stop(session=session_name)


async def test_file_init_auto_starts_session(tmp_path):
    """Test hol_file_init auto-starts HOL session if not running."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    session_name = "auto_start_test"

    # Ensure session doesn't exist
    await hol_stop(session=session_name)

    try:
        # hol_file_init should auto-start session
        result = await hol_file_init(file=str(test_file), session=session_name)

        # Should succeed and show verification status
        assert "Theorems:" in result
        assert "Verified:" in result

        # Verify session is now running
        sessions_result = await hol_sessions()
        assert session_name in sessions_result
        assert "running" in sessions_result
    finally:
        await hol_stop(session=session_name)


async def test_state_at_after_file_edit(tmp_path):
    """Test hol_state_at works correctly after file content changes."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="edit_test")

        # First call to state_at - get state at needs_proof theorem
        result1 = await hol_state_at(session="edit_test", line=21, col=1)
        assert "Tactic" in result1

        # Modify the file - add a comment (cursor should detect change and reparse)
        content = test_file.read_text()
        new_content = content.replace(
            "(* Theorem with cheat for testing cheat detection *)",
            "(* MODIFIED: Theorem with cheat for testing cheat detection *)"
        )
        test_file.write_text(new_content)

        # Call state_at again - cursor should reparse the file
        result2 = await hol_state_at(session="edit_test", line=21, col=1)

        # Should still work (reparse successful)
        assert "Tactic" in result2
        # Should NOT error out
        assert "ERROR" not in result2 or "not within any theorem" not in result2
    finally:
        await hol_stop(session="edit_test")


# =============================================================================
# Process Group Tests
# =============================================================================


async def test_kill_process_group_kills_children(tmp_path):
    """Test that _kill_process_group kills child processes, not just parent.

    This is a regression test for the holmake OOM issue where timeout killed
    only the parent Holmake process, leaving child buildheap processes as
    orphans that consumed 10-30GB RAM each.
    """
    # Create a script that spawns a child and sleeps
    script = tmp_path / "spawn_child.sh"
    script.write_text("""\
#!/bin/bash
# Spawn a child that also sleeps
sleep 300 &
CHILD_PID=$!
echo "CHILD_PID=$CHILD_PID"
# Parent also sleeps
sleep 300
""")
    script.chmod(0o755)

    # Start the process in its own session (like holmake does)
    proc = await asyncio.create_subprocess_exec(
        str(script),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        start_new_session=True,
    )

    # Wait for child PID to be printed
    line = await asyncio.wait_for(proc.stdout.readline(), timeout=5.0)
    child_pid = int(line.decode().strip().split("=")[1])
    parent_pid = proc.pid

    # Verify both processes are running
    assert _pid_exists(parent_pid), "Parent should be running"
    assert _pid_exists(child_pid), "Child should be running"

    # Kill the process group
    await _kill_process_group(proc)

    # Give OS a moment to clean up
    await asyncio.sleep(0.1)

    # Verify BOTH are dead
    assert not _pid_exists(parent_pid), "Parent should be dead after killpg"
    assert not _pid_exists(child_pid), "Child should be dead after killpg"


async def test_kill_process_group_no_leak_on_none():
    """Test that _kill_process_group handles None gracefully."""
    # Should not raise
    await _kill_process_group(None)


async def test_kill_process_group_no_leak_on_exited(tmp_path):
    """Test that _kill_process_group handles already-exited process."""
    script = tmp_path / "exit_immediately.sh"
    script.write_text("#!/bin/bash\nexit 0\n")
    script.chmod(0o755)

    proc = await asyncio.create_subprocess_exec(
        str(script),
        start_new_session=True,
    )
    await proc.wait()  # Let it exit

    # Should not raise on already-exited process
    await _kill_process_group(proc)


def _pid_exists(pid: int) -> bool:
    """Check if a process with given PID exists."""
    try:
        os.kill(pid, 0)  # Signal 0 just checks existence
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # Process exists but we can't signal it


# =============================================================================
# CLI Tests
# =============================================================================


import subprocess


def test_parse_goals_json():
    """Test _parse_goals_json parses goals_json() output correctly."""
    from hol4_mcp.hol_cursor import FileProofCursor
    from hol4_mcp.hol_file_parser import HOLParseError

    # Create a minimal cursor just to test the parsing method
    class MockCursor(FileProofCursor):
        def __init__(self):
            pass  # Skip normal init

    cursor = MockCursor()

    # Empty goals
    assert cursor._parse_goals_json('{"ok":[]}\n') == []

    # New format with assumptions
    result = cursor._parse_goals_json('{"ok":[{"asms":["P","Q"],"goal":"R"}]}\n')
    assert result == [{"asms": ["P", "Q"], "goal": "R"}]

    # Multiple goals with assumptions
    result = cursor._parse_goals_json('{"ok":[{"asms":[],"goal":"A"},{"asms":["X"],"goal":"B"}]}\n')
    assert result == [{"asms": [], "goal": "A"}, {"asms": ["X"], "goal": "B"}]

    # Old format (just strings) for backwards compat
    result = cursor._parse_goals_json('{"ok":["A ⇒ A"]}\n')
    assert result == [{"asms": [], "goal": "A ⇒ A"}]

    # Error case - should raise exception
    with pytest.raises(HOLParseError, match="NO_PROOFS"):
        cursor._parse_goals_json('{"err":"NO_PROOFS"}\n')

    # With trailing val it = (): unit
    result = cursor._parse_goals_json('{"ok":[{"asms":[],"goal":"goal"}]}\nval it = (): unit\n')
    assert result == [{"asms": [], "goal": "goal"}]

    # Invalid JSON should raise exception
    with pytest.raises(HOLParseError):
        cursor._parse_goals_json('not json at all')


def test_cli_help():
    """Test that hol4-mcp --help works."""
    result = subprocess.run(
        ["hol4-mcp", "--help"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0
    assert "HOL4 MCP Server" in result.stdout
    assert "--transport" in result.stdout
    assert "--port" in result.stdout


def test_cli_main_function():
    """Test the main() function can be imported and called with --help."""
    from hol4_mcp.hol_mcp_server import main
    import sys

    # Temporarily replace sys.argv
    old_argv = sys.argv
    try:
        sys.argv = ["hol4-mcp", "--help"]
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0
    finally:
        sys.argv = old_argv
