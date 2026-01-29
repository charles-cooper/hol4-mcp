"""Tests for proof timing functionality."""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession
from hol4_mcp.hol_cursor import FileProofCursor, TraceEntry


@pytest.mark.asyncio
async def test_timed_step_json(hol_session: HOLSession):
    """Test timed_step_json returns timing with goal counts."""
    # Test timed_step_json
    output = await hol_session.send('timed_step_json "1 + 1;";', timeout=10)
    assert '{"ok":' in output
    assert '"real_ms"' in output
    assert '"usr_ms"' in output
    assert '"sys_ms"' in output
    assert '"goals_before"' in output
    assert '"goals_after"' in output


@pytest.mark.asyncio
async def test_execute_proof_traced(hol_session: HOLSession, tmp_path: Path):
    """Test FileProofCursor.execute_proof_traced with actual theorem."""
    # Create a test script with a simple theorem
    script = tmp_path / "testScript.sml"
    script.write_text("""
open boolTheory;

Theorem test_and_comm:
  !a b. a /\\ b ==> b /\\ a
Proof
  rpt strip_tac
  >> fs[]
QED
""")

    cursor = FileProofCursor(script, hol_session)
    result = await cursor.init()
    assert not result.get("error"), f"Init failed: {result.get('error')}"

    # Execute proof with tracing
    trace = await cursor.execute_proof_traced("test_and_comm")

    # Should have trace entries
    assert len(trace) > 0, "Expected at least one trace entry"
    assert all(isinstance(e, TraceEntry) for e in trace)
    assert all(e.real_ms >= 0 for e in trace)
    assert all(e.cmd for e in trace)  # Each entry has a command


@pytest.mark.asyncio
async def test_execute_proof_traced_empty(hol_session: HOLSession, tmp_path: Path):
    """Test execute_proof_traced returns empty for nonexistent theorem."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem test_trivial:
  T
Proof
  rw[]
QED
""")

    cursor = FileProofCursor(script, hol_session)
    await cursor.init()

    # Try to trace nonexistent theorem
    trace = await cursor.execute_proof_traced("nonexistent")
    assert trace == []


@pytest.mark.asyncio
async def test_trace_entry_fields(hol_session: HOLSession, tmp_path: Path):
    """Test TraceEntry has all expected fields."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem test_trivial:
  T
Proof
  rw[]
QED
""")

    cursor = FileProofCursor(script, hol_session)
    await cursor.init()

    trace = await cursor.execute_proof_traced("test_trivial")
    assert len(trace) >= 1

    entry = trace[0]
    assert hasattr(entry, 'cmd')
    assert hasattr(entry, 'real_ms')
    assert hasattr(entry, 'usr_ms')
    assert hasattr(entry, 'sys_ms')
    assert hasattr(entry, 'goals_before')
    assert hasattr(entry, 'goals_after')
    assert hasattr(entry, 'error')
    assert entry.error is None  # Successful tactic has no error


@pytest.mark.asyncio
async def test_timed_step_timeout(hol_session: HOLSession, tmp_path: Path):
    """Test that per-tactic timeout works in SML."""
    script = tmp_path / "testScript.sml"
    # Tactic that sleeps - guarantees timeout and yields to interrupt
    script.write_text("""
Theorem test_slow:
  T
Proof
  (fn g => (OS.Process.sleep (Time.fromReal 5.0); ALL_TAC g))
QED
""")

    timeout_sec = 0.5
    cursor = FileProofCursor(script, hol_session, tactic_timeout=timeout_sec)
    await cursor.init()

    trace = await cursor.execute_proof_traced("test_slow")
    assert len(trace) >= 1

    entry = trace[0]
    assert entry.error == "TIMEOUT"
    # real_ms should be approximately the timeout value (within 200ms tolerance)
    assert abs(entry.real_ms - int(timeout_sec * 1000)) < 200


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
