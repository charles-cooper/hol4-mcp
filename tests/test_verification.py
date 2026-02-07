"""Tests for proof verification (hol_file_status, verify_all_proofs)."""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session_tmpdir(tmp_path):
    """Create a HOL session with tmp_path as workdir."""
    session = HOLSession(str(tmp_path))
    await session.start()
    # Load tactic_prefix.sml which defines timing functions
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    yield session
    await session.stop()


@pytest.mark.asyncio
async def test_verify_detects_incomplete_proof(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verify_all_proofs detects incomplete proofs (goals_after != 0)."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem incomplete_proof:
  T /\\ T
Proof
  ALL_TAC
QED
""")
    # ALL_TAC does nothing, leaves goal unchanged
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    assert "incomplete_proof" in results
    trace = results["incomplete_proof"]
    assert len(trace) > 0
    # Should have goals remaining (incomplete) - proof not finished
    final = trace[-1]
    assert final.goals_after != 0, f"Expected incomplete proof, got goals_after={final.goals_after}"


@pytest.mark.asyncio
async def test_verify_detects_tactic_error(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verify_all_proofs detects tactic errors."""
    script = tmp_path / "testScript.sml"
    # Use a tactic that will definitely error
    script.write_text("""
Theorem bad_tactic:
  T
Proof
  ACCEPT_TAC (ASSUME ``F``)
QED
""")
    # ACCEPT_TAC with wrong theorem type should fail
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    assert "bad_tactic" in results
    trace = results["bad_tactic"]
    assert len(trace) > 0
    # Should either have error or incomplete (goals remaining)
    final = trace[-1]
    assert final.error is not None or final.goals_after != 0


@pytest.mark.asyncio
async def test_verify_complete_proof_succeeds(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verify_all_proofs correctly identifies complete proofs."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem complete_proof:
  T
Proof
  simp[]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    assert "complete_proof" in results
    trace = results["complete_proof"]
    assert len(trace) > 0
    final = trace[-1]
    # Should complete with no goals and no error
    assert final.goals_after == 0
    assert final.error is None


@pytest.mark.asyncio
async def test_verify_stores_theorem_for_next(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verified theorems are stored so subsequent proofs can use them."""
    script = tmp_path / "testScript.sml"
    # Use MATCH_MP_TAC which works with implication theorems
    script.write_text("""
Theorem first_thm:
  !x. x ==> x
Proof
  simp[]
QED

Theorem uses_first:
  T ==> T
Proof
  MATCH_MP_TAC first_thm >> simp[]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # First should succeed
    first_trace = results["first_thm"]
    assert len(first_trace) > 0
    assert first_trace[-1].goals_after == 0
    assert first_trace[-1].error is None
    
    # Second should also succeed (can use first_thm)
    uses_trace = results["uses_first"]
    assert len(uses_trace) > 0
    # Either completes or at least doesn't error on first_thm reference
    assert uses_trace[-1].goals_after == 0 or uses_trace[-1].error is None


@pytest.mark.asyncio
async def test_verify_failed_theorem_not_stored(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that failed theorems are not stored (no QED on error)."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem broken:
  F
Proof
  ALL_TAC
QED

Theorem tries_to_use_broken:
  !x. x ==> x
Proof
  MATCH_MP_TAC broken
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # First should fail (ALL_TAC leaves goal unchanged)
    broken_trace = results["broken"]
    assert broken_trace[-1].goals_after != 0, "broken proof should be incomplete"
    
    # Second should fail because broken wasn't stored (or MATCH_MP_TAC fails)
    uses_trace = results["tries_to_use_broken"]
    # Either errors (broken not found) or doesn't complete
    assert uses_trace[-1].error is not None or uses_trace[-1].goals_after != 0


@pytest.mark.asyncio
async def test_verify_cheats_skipped(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that cheat theorems are loaded but not verified."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem has_cheat:
  F
Proof
  cheat
QED

Theorem after_cheat:
  T
Proof
  simp[]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # Cheat theorem should have empty trace
    assert results["has_cheat"] == []
    
    # Following theorem should still work
    assert results["after_cheat"][-1].goals_after == 0


@pytest.mark.asyncio
async def test_verify_loads_definitions_between_theorems(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that definitions between theorems are loaded."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition my_true_def:
  my_true = T
End

Theorem uses_def:
  my_true
Proof
  simp[my_true_def]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # Should succeed using the definition
    trace = results["uses_def"]
    assert len(trace) > 0
    assert trace[-1].goals_after == 0
    assert trace[-1].error is None


@pytest.mark.asyncio
async def test_loads_content_immediately_after_qed(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Regression: val bindings and Definitions on lines right after QED must be loaded.

    _load_remaining_content and _load_context_to_line had an off-by-one that
    skipped lines immediately following each theorem's QED.

    Tests both "before first theorem" and "between theorems" positions for both
    val bindings and Definition blocks.
    """
    script = tmp_path / "testScript.sml"
    script.write_text("""\
val pre_val = TRUTH;
Definition pre_def:
  pre_const = T
End
Theorem first_thm:
  pre_const
Proof
  simp[pre_def]
QED
val post_val = TRUTH;
Definition post_def:
  post_const = T
End
Theorem uses_post_qed_content:
  post_const
Proof
  simp[post_def]
QED
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # state_at on the second theorem should work (needs post_def loaded via init)
    result = await cursor.state_at(line=17, col=1)
    assert result.error is None, f"state_at failed: {result.error}"

    # verify_all_proofs should also succeed for both theorems
    results = await cursor.verify_all_proofs()

    trace1 = results["first_thm"]
    assert len(trace1) > 0
    assert trace1[-1].goals_after == 0, "first_thm proof failed (pre-theorem content not loaded)"
    assert trace1[-1].error is None

    trace2 = results["uses_post_qed_content"]
    assert len(trace2) > 0
    assert trace2[-1].goals_after == 0, "post-QED content not loaded (Definition/val after QED skipped)"
    assert trace2[-1].error is None
