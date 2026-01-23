"""Tests for HOL proof cursor."""

import pytest
import shutil
import tempfile
from pathlib import Path
from unittest.mock import AsyncMock, Mock

from hol4_mcp.hol_cursor import ProofCursor, get_executable_content, get_script_dependencies, _parse_linearize_result
from hol4_mcp.hol_file_parser import TheoremInfo
from hol4_mcp.hol_session import HOLSession

FIXTURES_DIR = Path(__file__).parent / "fixtures"


async def _linearize_full(session: HOLSession, s: str) -> tuple[list[str], int | None]:
    """Helper to call linearize_to_cheat and return (tactics, offset)."""
    escaped = s.replace("\\", "\\\\").replace('"', '\\"')
    result = await session.send(f'linearize_to_cheat "{escaped}";')
    return _parse_linearize_result(result)


async def _linearize_helper(session: HOLSession, s: str) -> list[str]:
    """Helper to call linearize_to_cheat and parse result (tactics only)."""
    tactics, _ = await _linearize_full(session, s)
    return tactics


@pytest.fixture
def mock_theorems():
    """Common TheoremInfo list for cursor unit tests."""
    return [
        TheoremInfo("a", "Theorem", "P", 1, 3, 5, False),
        TheoremInfo("b", "Theorem", "Q", 10, 12, 14, True),
        TheoremInfo("c", "Theorem", "R", 20, 22, 24, True),
    ]


def test_proof_cursor_next_cheat(mock_theorems):
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
    cursor.position = 0
    # Finds first theorem with cheat
    assert cursor.next_cheat().name == "b"


def test_next_cheat_finds_earliest_cheat(mock_theorems):
    """Test next_cheat always finds first cheat in file order."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
    # Position at end of file, but first cheat (b) is earlier
    cursor.position = 2

    # Should find b (first cheat) regardless of current position
    thm = cursor.next_cheat()
    assert thm is not None
    assert thm.name == "b"
    assert cursor.position == 1


def test_next_cheat_returns_none_when_all_done():
    """Test next_cheat returns None when no theorems have cheats."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    # All theorems complete (no cheats)
    cursor.theorems = [
        TheoremInfo("a", "Theorem", "P", 1, 3, 5, False),
        TheoremInfo("b", "Theorem", "Q", 10, 12, 14, False),
        TheoremInfo("c", "Theorem", "R", 20, 22, 24, False),
    ]
    cursor.position = 2

    assert cursor.next_cheat() is None


def test_proof_cursor_goto(mock_theorems):
    """Test ProofCursor.goto jumps to theorem by name."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems
    cursor.position = 0

    # Jump to c
    thm = cursor.goto("c")
    assert thm.name == "c"
    assert cursor.position == 2

    # Jump back to a
    thm = cursor.goto("a")
    assert thm.name == "a"
    assert cursor.position == 0

    # Non-existent returns None
    assert cursor.goto("nonexistent") is None
    assert cursor.position == 0  # unchanged


def test_proof_cursor_status_cheated_theorems(mock_theorems):
    """Test ProofCursor.status shows all theorems with cheats (ground truth from file)."""
    session = Mock()
    cursor = ProofCursor(Path("/tmp/test.sml"), session)
    cursor.theorems = mock_theorems + [TheoremInfo("d", "Theorem", "S", 30, 32, 34, True)]
    cursor.position = 1  # at b

    status = cursor.status
    assert status["current"] == "b"
    # Shows all theorems with has_cheat=True (file state, not filtered by completed)
    # Line numbers are proof_start_line (where the proof body begins)
    assert status["cheated_theorems"] == [
        {"name": "b", "line": 12},
        {"name": "c", "line": 22},
        {"name": "d", "line": 32},
    ]  # a excluded (no cheat)


def test_get_executable_content_raw_sml():
    """Test get_executable_content with raw SML file (no Theory header)."""
    content = '''(* Comment *)
open HolKernel boolLib;

Definition foo_def:
  foo x = x + 1
End

Theorem bar:
  foo 0 = 1
Proof
  rw[foo_def]
QED
'''
    # Get content up to line 8 (before Theorem bar on line 8)
    result = get_executable_content(content, 8)
    assert "open HolKernel" in result
    assert "Definition foo_def" in result
    assert "Theorem bar" not in result


def test_get_executable_content_script_format():
    """Test get_executable_content includes Theory/Ancestors header."""
    content = '''Theory myTheory
Ancestors
  listTheory arithmeticTheory

(* First executable content *)
Definition foo_def:
  foo x = x + 1
End

Theorem bar:
  foo 0 = 1
Proof
  cheat
QED
'''
    # Get content up to line 10 (Theorem bar starts on line 10)
    result = get_executable_content(content, 10)
    # Header is now included (sets up environment)
    assert "Theory myTheory" in result
    assert "Ancestors" in result
    assert "listTheory" in result
    assert "(* First executable content *)" in result
    assert "Definition foo_def" in result
    # But not the theorem we're about to prove
    assert "Theorem bar" not in result


def test_get_executable_content_multiline_ancestors():
    """Test get_executable_content includes multi-line Ancestors header."""
    content = '''Theory bigTheory
Ancestors
  list rich_list
  arithmetic prim_rec
  set pred_set

(* Start here *)
val x = 1;
'''
    result = get_executable_content(content, 10)
    # Header is now included (sets up environment)
    assert "Theory" in result
    assert "Ancestors" in result
    assert "list rich_list" in result
    assert "(* Start here *)" in result


@pytest.mark.asyncio
async def test_get_script_dependencies():
    """Test get_script_dependencies with fixture file."""
    fixture = FIXTURES_DIR / "testScript.sml"
    if not fixture.exists():
        pytest.skip("Fixture not found")

    deps = await get_script_dependencies(fixture)
    # Should return list of dependencies
    assert isinstance(deps, list)
    # Basic HOL deps should be present
    assert any("HolKernel" in d or "boolLib" in d for d in deps)


# =============================================================================
# ProofCursor Integration Tests (require HOL)
# =============================================================================

async def test_proof_cursor_initialize():
    """Test ProofCursor.initialize with real HOL session."""
    with tempfile.TemporaryDirectory() as d:
        # Copy fixture to temp dir (so we don't modify original)
        test_file = Path(d) / "testScript.sml"
        shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            result = await cursor.initialize()

            # Should position at first cheat (needs_proof)
            assert "needs_proof" in result
            assert cursor.current().name == "needs_proof"
            assert cursor.current().has_cheat


async def test_proof_cursor_start_current():
    """Test ProofCursor.start_current sets up goaltree."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            result = await cursor.start_current()
            assert "Ready" in result or "needs_proof" in result

            # Verify goaltree is active
            state = await session.send("top_goals();", timeout=10)
            assert "goal" in state.lower() or "+" in state  # Goals present


@pytest.mark.asyncio
async def test_extract_proof_rejects_error_output():
    """Test extract_proof returns error when p() fails."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        original = """open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
"""
        test_file.write_text(original)

        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Agent abandons the proof
            await session.send("drop();")

            # Now extract_proof calls p() which errors
            result = await cursor.extract_proof()

            # Should return error dict
            assert "error" in result
            assert "No proof found" in result["error"]


@pytest.mark.asyncio
async def test_extract_proof_rejects_anonymous():
    """Test extract_proof rejects proofs with <anonymous> tactics."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Use e() instead of etq - loses tactic name
            await session.send("e(REWRITE_TAC[]);")

            result = await cursor.extract_proof()

            assert "error" in result
            assert "anonymous" in result["error"].lower()


@pytest.mark.asyncio
async def test_extract_proof_returns_proof():
    """Test extract_proof returns proof dict on success."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Complete the proof properly
            await session.send('etq "REWRITE_TAC[]";')

            result = await cursor.extract_proof()

            # Should return proof dict
            assert "error" not in result
            assert result["theorem"] == "foo"
            assert "proof" in result


@pytest.mark.asyncio
async def test_tactics_before_cheat_subgoal_replay():
    """Test that >- structured tactics replay correctly via linearize_to_cheat."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # A proof with >- structure where >- matters (conj_tac creates 2 goals)
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem conj_example:
  T /\\ T
Proof
  conj_tac >- simp[] \\\\
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            thm = cursor.current()
            assert thm.name == "conj_example"

            # start_current uses linearize_to_cheat -> ["conj_tac", "simp[]"]
            result = await cursor.start_current()
            assert "2 tactics auto-applied" in result, f"Expected linearize replay: {result}"

            # Check the goaltree state after replay
            p_output = await session.send("p();")
            print(f"Proof body: {thm.proof_body}")
            print(f"p() output: {p_output}")

            # p() reconstructs >- because conj_tac created 2 goals and simp[] solved first
            assert ">-" in p_output, f"Expected >- in output, got: {p_output}"


@pytest.mark.asyncio
async def test_start_current_nested_cheat():
    """Test start_current navigates to nested cheat via linearize_to_cheat."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # Nested cheat that extract_before_cheat can't handle
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem nested:
  (A ==> B) ==> (B ==> C) ==> A ==> C
Proof
  rpt strip_tac >-
   (first_x_assum irule \\\\
    cheat)
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            thm = cursor.current()
            assert thm.name == "nested"

            # start_current should use linearize_to_cheat for this nested structure
            result = await cursor.start_current()
            # Should report auto-applied tactics
            assert "tactics auto-applied" in result, f"Expected auto-applied: {result}"

            # Verify we're at the right goal state (inside the >- branch)
            goals = await session.send("top_goals();")
            # After rpt strip_tac and first_x_assum irule, we should have goal B
            assert "B" in goals, f"Expected goal B, got: {goals}"


@pytest.mark.asyncio
async def test_start_current_error_recovery():
    """Test start_current reports which tactic failed during replay."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # Proof with a tactic that will fail
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem will_fail:
  T
Proof
  simp[] >-
   (FAIL_TAC "deliberate" \\\\
    cheat)
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            result = await cursor.start_current()
            # Should report which tactic failed
            assert "ERROR" in result, f"Expected error: {result}"
            assert "FAIL_TAC" in result or "2/2" in result, f"Should identify failed tactic: {result}"


@pytest.mark.asyncio
async def test_cheat_finder_no_exhaustivity_warnings():
    """Test that cheat_finder.sml loads without pattern match warnings."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Session start loads cheat_finder.sml - check no warnings in output
            # by re-loading and checking output
            cheat_finder = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers" / "cheat_finder.sml"
            result = await session.send(cheat_finder.read_text(), timeout=30)
            # Poly/ML warnings contain "Warning:" for non-exhaustive matches
            assert "Warning" not in result, f"Got warnings: {result}"
            assert "warning" not in result.lower() or "dropWhile" in result, f"Got warnings: {result}"


@pytest.mark.asyncio
async def test_extract_before_cheat_edge_cases():
    """Test extract_before_cheat handles various edge cases."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            async def extract(s: str) -> str:
                escaped = s.replace("\\", "\\\\").replace('"', '\\"')
                result = await session.send(f'extract_before_cheat "{escaped}";')
                # Parse val it = "...": string
                for line in result.split('\n'):
                    if 'val it = "' in line and '": string' in line:
                        start = line.index('"') + 1
                        end = line.rindex('": string')
                        return line[start:end].replace("\\\\", "\\")
                return ""

            # Basic: each operator type
            assert await extract("cheat") == ""
            assert await extract("simp[] \\\\ cheat") == "simp[]"
            assert await extract("simp[] \\\\ CHEAT") == "simp[]"
            assert await extract("strip_tac >> cheat") == "strip_tac"
            assert await extract("rw[] >- cheat") == "rw[]"

            # Multiple cheats - extracts before FIRST
            assert await extract("simp[] \\\\ cheat \\\\ gvs[] \\\\ cheat") == "simp[]"

            # Nested structure
            assert await extract("(strip_tac \\\\ simp[]) \\\\ cheat") == "(strip_tac \\\\ simp[])"

            # Chained subgoals and mixed operators
            assert await extract("conj_tac >- simp[] >- cheat") == "conj_tac >- simp[]"
            assert await extract("a >> b \\\\ c >- d >> cheat") == "a >> b \\\\ c >- d"

            # Empty input
            assert await extract("") == "" and await extract("   ") == ""

            # "cheat" in identifier/backquote (should find real cheat tactic)
            assert await extract("simp[cheat_def] \\\\ cheat") == "simp[cheat_def]"
            assert await extract("foo `cheat` \\\\ cheat") == "foo `cheat`"

            # Embedded quotes (must stay escaped for etq)
            result = await extract('rename1 "x" \\\\ cheat')
            assert 'rename1' in result and 'x' in result

            # Known limitation: SML keywords (if/case/fn) in backquotes break TacticParse
            assert await extract("qexists_tac `if x then y else z` \\\\ cheat") == ""
            assert await extract("foo `case x of _ => y` \\\\ cheat") == ""
            assert await extract("foo `fn x => x` \\\\ cheat") == ""
            assert await extract("qexists_tac `x` \\\\ cheat") == "qexists_tac `x`"  # simple backquote works

            # Test cases for nested structures - should return empty (invalid prefix)
            assert await extract("strip_tac >- (simp[] \\\\ cheat)") == ""
            assert await extract("(a >- b >- cheat)") == ""


@pytest.mark.asyncio
async def test_start_current_with_backslash_tactic():
    """Test tactics with /\\ in terms are escaped properly for etq."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # A proof with /\ in the goal (requires escaping for SML strings)
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem conj_true:
  T /\\ T
Proof
  simp[] \\\\
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Check theorem was found
            thm = cursor.current()
            assert thm.name == "conj_true"

            # start_current should work - the /\ in the goal needs escaping
            result = await cursor.start_current()

            # Should not error - if escaping fails, we'd see an SML parse error
            assert "ERROR" not in result
            assert "Ready" in result or "conj_true" in result

            # Verify the pre-cheat tactic was replayed
            p_output = await session.send("p();")
            assert "simp" in p_output


@pytest.mark.asyncio
async def test_drop_all_clears_stacked_goaltrees():
    """Test drop_all() clears all stacked goaltrees."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Stack multiple goaltrees
            await session.send('gt `A ==> A`;')
            await session.send('gt `B ==> B`;')
            await session.send('gt `C ==> C`;')

            # Verify 3 proofs on stack
            status = await session.send('status();')
            assert "3 proofs" in status

            # drop_all should clear everything
            result = await session.send('drop_all();')
            assert "no proofs" in result.lower()

            # Verify empty
            status = await session.send('status();')
            assert "no proofs" in status.lower()

            # Can start fresh
            await session.send('gt `X ==> X`;')
            status = await session.send('status();')
            assert "1 proof" in status


@pytest.mark.asyncio
async def test_drop_all_idempotent():
    """Test drop_all() is safe to call on empty state."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Call drop_all on empty state - should not error
            result = await session.send('drop_all();')
            assert "no proofs" in result.lower()

            # Call again - still safe
            result = await session.send('drop_all();')
            assert "no proofs" in result.lower()


@pytest.mark.asyncio
async def test_start_current_clears_stacked_proofs():
    """Test start_current() uses drop_all() to clear stacked proofs."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib;

Theorem foo:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Enter goaltree for foo (like MCP tool does)
            await cursor.start_current()

            # Stack extra goaltrees (simulating agent doing manual gt calls)
            await session.send('gt `A ==> A`;')
            await session.send('gt `B ==> B`;')

            # Verify we have multiple proofs now
            status = await session.send('status();')
            assert "3 proof" in status  # original + 2 extra

            # start_current should clear all and start fresh
            result = await cursor.start_current()
            assert "ERROR" not in result

            # Should have exactly 1 proof now (foo)
            status = await session.send('status();')
            assert "1 proof" in status

            # And it should be the right goal
            goals = await session.send('top_goals();')
            assert "T" in goals


@pytest.mark.asyncio
async def test_extract_proof_finds_earlier_cheat():
    """Test extract_proof finds cheats earlier in file after completing later one."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # Two theorems with cheats
        test_file.write_text("""open HolKernel boolLib;

Theorem first:
  T
Proof
  cheat
QED

Theorem second:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            # Jump to second theorem (skipping first)
            cursor.goto("second")
            await cursor.start_current()

            # Complete second theorem
            await session.send('etq "simp[]";')
            result = await cursor.extract_proof()

            assert "error" not in result
            assert result["theorem"] == "second"
            assert "proof" in result


@pytest.mark.asyncio
async def test_linearize_to_cheat_basic():
    """Test linearize_to_cheat handles basic cases."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Empty/just cheat - offset is 0 (cheat at start)
            tactics, offset = await _linearize_full(session, "cheat")
            assert tactics == []
            assert offset == 0

            tactics, offset = await _linearize_full(session, "CHEAT")
            assert tactics == []
            assert offset == 0

            # Simple linear chain - should return compound with >>
            tactics, offset = await _linearize_full(session, "simp[] \\\\ cheat")
            assert tactics == ["simp[]"], f"Got {tactics}"
            assert offset == 10, f"Got offset {offset}"  # "simp[] \\ " = 10 chars

            tactics, offset = await _linearize_full(session, "strip_tac >> simp[] \\\\ cheat")
            assert tactics == ["strip_tac >> simp[]"], f"Got {tactics}"
            assert offset == 23, f"Got offset {offset}"

            # >- structure - should split at >- boundary
            tactics, offset = await _linearize_full(session, "conj_tac >- simp[] \\\\ cheat")
            # After conj_tac, >- only applies simp[] to first goal
            # So we emit conj_tac, then simp[]
            assert tactics == ["conj_tac", "simp[]"], f"Got {tactics}"
            assert offset == 22, f"Got offset {offset}"


@pytest.mark.asyncio
async def test_linearize_to_cheat_nested():
    """Test linearize_to_cheat handles nested >- structures."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            # Nested cheat inside >- arm
            # This is the key case that extract_before_cheat returns "" for
            tactics, offset = await _linearize_full(session, "strip_tac >- (simp[] \\\\ cheat)")
            assert tactics == ["strip_tac", "simp[]"], f"Got {tactics}"
            assert offset == 24, f"Got offset {offset}"

            # Multiple levels of nesting
            tactics, offset = await _linearize_full(session, "a >- (b >- (c \\\\ cheat))")
            assert tactics == ["a", "b", "c"], f"Got {tactics}"
            assert offset == 17, f"Got offset {offset}"

            # Mixed >> and >- before nested cheat
            tactics, offset = await _linearize_full(session, "a >> b >- (c >> d \\\\ cheat)")
            assert tactics == ["a >> b", "c >> d"], f"Got {tactics}"
            assert offset == 21, f"Got offset {offset}"

            # by tactic - cheat after by
            tactics, offset = await _linearize_full(session, "`A` by simp[] \\\\ cheat")
            assert tactics == ["`A` by simp[]"], f"by: Got {tactics}"
            assert offset == 17, f"by: Got offset {offset}"

            # sg tactic - sg is opaque, so it forms a >> chain with simp[]
            tactics, offset = await _linearize_full(session, "sg `A` \\\\ simp[] \\\\ cheat")
            assert tactics == ["sg `A` >> simp[]"], f"sg: Got {tactics}"
            assert offset == 20, f"sg: Got offset {offset}"

            # >| (THENL) - cheat in second arm
            tactics, offset = await _linearize_full(session, "conj_tac >| [simp[], cheat]")
            assert tactics == ["conj_tac", "simp[]"], f">|: Got {tactics}"
            assert offset == 21, f">|: Got offset {offset}"

            # >| with cheat in first arm
            tactics, offset = await _linearize_full(session, "conj_tac >| [cheat, simp[]]")
            assert tactics == ["conj_tac"], f">| first: Got {tactics}"
            assert offset == 13, f">| first: Got offset {offset}"

            # suffices_by - like by but with nested Group/ThenLT/LReverse structure
            tactics, offset = await _linearize_full(session, "`A` suffices_by simp[] \\\\ cheat")
            assert tactics == ["`A` suffices_by simp[]"], f"suffices_by: Got {tactics}"
            assert offset == 26, f"suffices_by: Got offset {offset}"


@pytest.mark.asyncio
async def test_linearize_orelse():
    """Test linearize_to_cheat handles ORELSE/First constructs."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            lin = lambda s: _linearize_helper(session, s)

            # ORELSE - cheat in second alternative
            # Should NOT emit first alternative (it failed, that's why we're in second)
            result = await lin("simp[] ORELSE cheat")
            assert result == [], f"ORELSE: Got {result}"

            # ORELSE - cheat in first alternative
            result = await lin("cheat ORELSE simp[]")
            assert result == [], f"ORELSE first: Got {result}"

            # ORELSE with prefix before cheat in second alt
            result = await lin("simp[] ORELSE (strip_tac \\\\ cheat)")
            assert result == ["strip_tac"], f"ORELSE nested: Got {result}"

            # Nested ORELSE inside >-
            result = await lin("conj_tac >- (simp[] ORELSE cheat)")
            assert result == ["conj_tac"], f">- ORELSE: Got {result}"


@pytest.mark.asyncio
async def test_linearize_try_repeat():
    """Test linearize_to_cheat handles TRY and REPEAT constructs."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            lin = lambda s: _linearize_helper(session, s)

            # TRY - cheat inside TRY
            result = await lin("TRY cheat")
            assert result == [], f"TRY: Got {result}"

            # TRY with tactics before cheat
            result = await lin("TRY (simp[] \\\\ cheat)")
            assert result == ["simp[]"], f"TRY nested: Got {result}"

            # Prefix then TRY with cheat
            result = await lin("strip_tac \\\\ TRY cheat")
            assert result == ["strip_tac"], f"prefix TRY: Got {result}"

            # REPEAT - cheat inside REPEAT
            result = await lin("REPEAT cheat")
            assert result == [], f"REPEAT: Got {result}"

            # rpt is recognized as REPEAT by TacticParse
            result = await lin("rpt cheat")
            assert result == [], f"rpt: Got {result}"

            result = await lin("rpt (simp[] \\\\ cheat)")
            assert result == ["simp[]"], f"rpt nested: Got {result}"


@pytest.mark.asyncio
async def test_linearize_goal_selectors():
    """Test linearize_to_cheat handles goal selector syntax [n] >-."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            lin = lambda s: _linearize_helper(session, s)

            # Single goal selector
            result = await lin("[1] >- cheat")
            assert result == ["[1]"], f"[1]>-: Got {result}"

            # Multiple goal selector
            result = await lin("[1,2] >- simp[] \\\\ cheat")
            assert result == ["[1,2]", "simp[]"], f"[1,2]>-: Got {result}"

            # Nested tactics after selector
            result = await lin("[1] >- (strip_tac \\\\ cheat)")
            assert result == ["[1]", "strip_tac"], f"[1]>- nested: Got {result}"


@pytest.mark.asyncio
async def test_linearize_function_applications():
    """Test linearize_to_cheat with common tactic function applications."""
    with tempfile.TemporaryDirectory() as d:
        async with HOLSession(d) as session:
            lin = lambda s: _linearize_helper(session, s)

            # ntac - LIMITATION: parses as single opaque span, cheat not detected
            # TacticParse doesn't parse inside arbitrary function applications
            result = await lin("ntac 3 cheat")
            # Returns whole thing because cheat isn't found as separate AST node
            assert result == ["ntac 3 cheat"], f"ntac (limitation): Got {result}"

            # But ntac with \\ works because \\ is parsed
            result = await lin("ntac 3 simp[] \\\\ cheat")
            assert result == ["ntac 3 simp[]"], f"ntac \\\\: Got {result}"

            # pop_assum - common tactic with function argument
            result = await lin("pop_assum mp_tac \\\\ cheat")
            assert result == ["pop_assum mp_tac"], f"pop_assum: Got {result}"

            # first_x_assum with drule
            result = await lin("first_x_assum drule \\\\ cheat")
            assert result == ["first_x_assum drule"], f"first_x_assum: Got {result}"

            # qexists_tac with quoted term
            result = await lin("qexists_tac `x` \\\\ cheat")
            assert result == ["qexists_tac `x`"], f"qexists_tac: Got {result}"


@pytest.mark.asyncio
async def test_linearize_to_cheat_replay():
    """Test that linearized tactics actually reach the correct goal state."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # A proof with nested >- where cheat is inside a branch
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem nested_conj:
  (A /\\ B) /\\ C ==> A /\\ B /\\ C
Proof
  strip_tac >-
   (strip_tac \\\\
    cheat) \\\\
  simp[]
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            thm = cursor.current()
            assert thm.name == "nested_conj"
            assert thm.has_cheat

            # The proof structure:
            # strip_tac >- (strip_tac \\ cheat) \\ simp[]
            # Cheat is inside the >- arm

            # extract_before_cheat would return "" (nested cheat)
            from hol4_mcp.hol_session import escape_sml_string
            escaped = escape_sml_string(thm.proof_body)
            extract_result = await session.send(f'extract_before_cheat "{escaped}";')
            # Parse the result
            for line in extract_result.split('\n'):
                if 'val it = "' in line:
                    # Empty string means extraction failed (expected for nested)
                    assert '""' in line or 'val it = "": string' in line, f"Expected empty, got: {line}"
                    break

            # But linearize_to_cheat should work
            lin_result = await session.send(f'linearize_to_cheat "{escaped}";')
            print(f"Linearize result: {lin_result}")

            # Parse result using shared helper
            tactics, offset = _parse_linearize_result(lin_result)
            print(f"Parsed tactics: {tactics}, offset: {offset}")
            assert len(tactics) >= 2, f"Expected at least 2 tactics, got {tactics}"

            # Now apply the tactics and verify we reach the cheat position
            await session.send('drop_all();')
            goal = thm.goal.replace('\n', ' ').strip()
            await session.send(f'gt `{goal}`;')

            for tac in tactics:
                tac_escaped = escape_sml_string(tac.replace('\n', ' '))
                result = await session.send(f'etq "{tac_escaped}";')
                print(f"Applied: {tac}, result: {result[:200]}")
                assert "Exception" not in result, f"Tactic failed: {result}"

            # After replay, we should be at the cheat position
            # The remaining goal should be provable (it's the A from the conjunction)
            goals = await session.send('top_goals();')
            print(f"Goals after replay: {goals}")
            # Should have at least one goal remaining (where cheat was)
            assert "[]" not in goals or "goal" in goals.lower()


@pytest.mark.asyncio
async def test_start_current_loads_intermediate_context():
    """Test start_current loads definitions between theorems."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # First theorem, then a definition, then second theorem that uses it
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem first:
  T
Proof
  cheat
QED

Definition my_val_def:
  my_val = (5:num)
End

Theorem uses_def:
  my_val = 5
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()
            await cursor.start_current()

            # Complete first theorem
            await session.send('etq "simp[]";')
            result = await cursor.extract_proof()
            assert result["theorem"] == "first"

            # Move to uses_def (in real flow, reenter would do this after file edit)
            cursor.goto("uses_def")

            # Now start_current for uses_def - should load my_val_def
            start_result = await cursor.start_current()
            assert "ERROR" not in start_result

            # Prove using the definition - this would fail if def wasn't loaded
            tac_result = await session.send('etq "simp[my_val_def]";')
            assert "Exception" not in tac_result
            assert "error" not in tac_result.lower()

            # Verify proof completed (empty goal list)
            goals = await session.send("top_goals();")
            assert "[]" in goals  # empty goal list


@pytest.mark.asyncio
async def test_cheat_line_computed_on_init():
    """Test cheat_line is computed from SML parser during initialization."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        # Cheat is on line 7 (after 2 tactics)
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem foo:
  T
Proof
  strip_tac >>
  simp[] >>
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            thm = cursor.current()
            assert thm.name == "foo"
            assert thm.has_cheat
            # Cheat is at line 8 (line 5 is proof start, +3 for the two tactics and cheat)
            assert thm.cheat_line == 8, f"Expected cheat at line 8, got {thm.cheat_line}"


@pytest.mark.asyncio
async def test_cheat_line_first_line():
    """Test cheat_line when cheat is first thing in proof."""
    with tempfile.TemporaryDirectory() as d:
        test_file = Path(d) / "testScript.sml"
        test_file.write_text("""open HolKernel boolLib bossLib;

Theorem bar:
  T
Proof
  cheat
QED
""")
        async with HOLSession(d) as session:
            cursor = ProofCursor(test_file, session)
            await cursor.initialize()

            thm = cursor.current()
            assert thm.cheat_line == 6, f"Expected cheat at line 6, got {thm.cheat_line}"
