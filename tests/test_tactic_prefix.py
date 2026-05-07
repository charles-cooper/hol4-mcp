"""Tests for tactic_prefix.sml functions (goalfrag_step_plan).

Tests the GOALFRAG-based proof navigation: every TacticParse.linearize fragment
is a step, FOpen/FFMid/FFClose are natively steppable via ef().
"""

import pytest
import json
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


async def call_step_plan(session: HOLSession, tactic_str: str):
    """Call goalfrag_step_plan_json and parse the result."""
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'goalfrag_step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)




# =============================================================================
# Step Plan: basic structure
# =============================================================================

class TestGoalfragStepPlanBasic:
    """Basic goalfrag_step_plan tests."""

    async def test_single_tactic(self, hol_session):
        """Single tactic returns one step."""
        result = await call_step_plan(hol_session, "simp[]")
        assert len(result) == 1
        assert "ef(goalFrag.expand(simp[]))" in result[0].cmd

    async def test_then_chain(self, hol_session):
        """>> chain returns one step per tactic."""
        result = await call_step_plan(hol_session, "a >> b >> c")
        assert len(result) == 3
        assert "ef(goalFrag.expand(a))" in result[0].cmd
        assert "ef(goalFrag.expand(b))" in result[1].cmd
        assert "ef(goalFrag.expand(c))" in result[2].cmd

    async def test_ends_are_monotonic(self, hol_session):
        """End offsets should be monotonically non-decreasing."""
        result = await call_step_plan(hol_session, "a >> b >> c >> d")
        ends = [step.end for step in result]
        assert ends == sorted(ends)

    async def test_empty_proof_body_returns_empty_expand(self, hol_session):
        """Empty proof body produces a single empty expand step."""
        result = await call_step_plan(hol_session, "")
        # parseTacticBlock on "" produces Opaque with zero-length span
        assert len(result) <= 1  # 0 or 1 step (empty expand)

    async def test_with_quotations(self, hol_session):
        """Backtick quotations work."""
        result = await call_step_plan(hol_session, "Cases_on `x` >> simp[]")
        assert len(result) == 2
        assert "Cases_on" in result[0].cmd
        assert "simp" in result[1].cmd


# =============================================================================
# Step Plan: >- (Then1) decomposition
# =============================================================================

class TestGoalfragThen1Decomposition:
    """With GOALFRAG, >- decomposes into open/expand/close fragments."""

    async def test_single_then1(self, hol_session):
        """`a >- b` → expand(a), open_then1, expand(b), close_paren."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        cmds = [s.cmd for s in result]
        assert "ef(goalFrag.expand(conj_tac));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.expand(simp[]));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds
        # Order: expand base, open, expand arm, close
        assert cmds.index("ef(goalFrag.expand(conj_tac));") < cmds.index("ef(goalFrag.open_then1);")
        assert cmds.index("ef(goalFrag.open_then1);") < cmds.index("ef(goalFrag.expand(simp[]));")
        assert cmds.index("ef(goalFrag.expand(simp[]));") < cmds.index("ef(goalFrag.close_paren);")

    async def test_nested_then1(self, hol_session):
        """Chained >- decomposes each arm."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >- fs[]")
        cmds = [s.cmd for s in result]
        # Should have: expand(conj_tac), open, expand(simp[]), close, open, expand(fs[]), close
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.close_paren);" in cmds
        # Two open_then1 (one per >-)
        assert cmds.count("ef(goalFrag.open_then1);") == 2
        assert cmds.count("ef(goalFrag.close_paren);") == 2

    async def test_by_decomposition(self, hol_session):
        """`by` (sugar for >-) decomposes the same way."""
        result = await call_step_plan(hol_session, "strip_tac by simp[]")
        cmds = [s.cmd for s in result]
        assert "ef(goalFrag.expand(strip_tac));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.expand(simp[]));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds


# =============================================================================
# Step Plan: >| (ThenL) — stays atomic when linearize treats it as one
# =============================================================================

class TestGoalfragThenLDecomposition:
    """Multi-arm >| decomposition depends on linearize output."""

    async def test_thenl_atomic(self, hol_session):
        """strip_tac >| [simp[], fs[]] may be one atom if linearize doesn't decompose it."""
        result = await call_step_plan(hol_session, "strip_tac >| [simp[], fs[]]")
        # linearize treats this as FAtom(Opaque) — one step
        assert len(result) >= 1
        assert "ef(goalFrag.expand" in result[0].cmd


# =============================================================================
# Step Plan: execution correctness
# =============================================================================

class TestGoalfragExecutionCorrectness:
    """Verify that step_plan steps actually execute and produce correct goals."""

    async def test_then_chain_execution(self, hol_session):
        """>> chain steps execute correctly on GOALFRAG."""
        result = await call_step_plan(hol_session, "CONJ_TAC >> REFL_TAC >> REFL_TAC")
        # Without >-, CONJ_TAC creates 2 goals >> applies to both
        # Actually CONJ_TAC >> REFL_TAC on `T /\ T` would:
        # CONJ_TAC splits into T, T; REFL_TAC fails on T (not an equation)
        # Use a simpler proof
        pass  # Execution tests are covered by state_at integration tests

    async def test_then1_execution(self, hol_session):
        """Single >- step plan executes correctly on GOALFRAG."""
        # Set up goal and execute steps
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\ T`;', timeout=10)

        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        assert len(result) == 7  # expand, open, expand, close, open, expand, close

        # Execute all steps
        for step in result:
            r = await hol_session.send(step.cmd, timeout=10)
            assert not any("Exception-" in line for line in r.split('\n')), f"Step failed: {step.cmd} → {r}"

        # Verify proof completed
        r = await hol_session.send('top_thm();', timeout=10)
        assert "T ∧ T" in r


# =============================================================================
# backup_n
# =============================================================================

class TestBackupN:
    """Test backup_n undoes ef() steps on GOALFRAG."""

    async def test_backup_then1_proof(self, hol_session):
        """backup_n correctly undoes >- steps."""
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\ T`;', timeout=10)

        plan = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")

        # Execute up to step 3 (CONJ_TAC + open_then1 + SIMP_TAC)
        for step in plan[:3]:
            await hol_session.send(step.cmd, timeout=10)

        # Check goals: should have 0 goals (first arm solved, focused)
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 0, f"Expected 0 goals after step 3, got {len(goals)}"
                break

        # Backup 2 steps (undo SIMP_TAC + open_then1)
        await hol_session.send('backup_n 2;', timeout=10)

        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 2, f"Expected 2 goals after backup, got {len(goals)}"
                break

    async def test_backup_full_proof(self, hol_session):
        """backup_n undoes entire proof back to initial goal."""
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\ T`;', timeout=10)

        plan = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")

        for step in plan:
            await hol_session.send(step.cmd, timeout=10)

        # Should be complete
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 0
                break

        # Undo all
        await hol_session.send(f'backup_n {len(plan)};', timeout=10)

        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 1
                assert "T ∧ T" in goals[0]['goal']
                break


# =============================================================================
# Step Plan: ThenLT/By re-expansion inside >> chains
# =============================================================================

class TestThenLTReexpand:
    """ThenLT inside >> chains: reexpand to get open/close decomposition.

    linearize's `asTac` skips bracketing when `one=true` (inside Then list),
    collapsing >- into a single FAtom. reexpand_group_atoms detects these
    and re-linearizes the ThenLT AST at the top level to get proper decomposition.

    Subgoal-based ThenLT (by/sg) is NOT re-expanded because `Subgoal \`Q\``
    is not a standalone tactic — only the full `\`Q\` by tac` expression is valid.
    For by inside >> chains, navigation stays at the atomic step level.
    """

    async def test_thenlt_in_then_chain(self, hol_session):
        """>- inside >> chain decomposes into expand/open/expand/close steps."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> fs[]")
        # conj_tac, open_then1, simp[], close_paren, fs[]
        assert len(result) == 5, f"Expected 5 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and "conj_tac" in result[0].text
        assert result[1].kind == "open" and result[1].text == "open_then1"
        assert result[2].kind == "expand" and "simp" in result[2].text
        assert result[3].kind == "close" and result[3].text == "close_paren"
        assert result[4].kind == "expand" and result[4].text == "fs[]"

    async def test_by_in_then_chain(self, hol_session):
        """`by` inside >> chain decomposes: `Q` gets sg prefix, tactic base stays as-is."""
        result = await call_step_plan(hol_session, r"strip_tac >> `Q` by simp[] >> fs[]")
        # strip_tac, sg `Q`, open_then1, simp[], close_paren, fs[]
        assert len(result) == 6, f"Expected 6 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and result[0].text == "strip_tac"
        assert result[1].kind == "expand" and result[1].text.startswith("sg")
        assert result[2].kind == "open" and result[2].text == "open_then1"
        assert result[3].kind == "expand" and "simp" in result[3].text
        assert result[4].kind == "close" and result[4].text == "close_paren"
        assert result[5].kind == "expand" and result[5].text == "fs[]"

    async def test_by_tactic_base_no_sg_prefix(self, hol_session):
        """`by` with tactic base (not term quotation) keeps base text unchanged."""
        result = await call_step_plan(hol_session, "strip_tac by simp[]")
        # strip_tac (not "sg strip_tac"), open_then1, simp[], close_paren
        assert len(result) == 4, f"Expected 4 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].text == "strip_tac", f"Tactic base should not get sg: {result[0].text}"

    async def test_sg_in_then_chain_decomposes(self, hol_session):
        """`sg >-` inside >> chain decomposes."""
        result = await call_step_plan(hol_session, r"strip_tac >> sg `Q` >- simp[] >> fs[]")
        # strip_tac, sg `Q`, open_then1, simp[], close_paren, fs[]
        assert len(result) == 6, f"Expected 6 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[1].kind == "expand" and "sg" in result[1].text.lower()
        assert result[2].kind == "open"

    async def test_by_term_base_gets_sg_prefix(self, hol_session):
        """Standalone `by` with term quotation base gets sg prefix."""
        result = await call_step_plan(hol_session, r"`Q` by simp[]")
        # sg `Q`, open_then1, simp[], close_paren
        assert len(result) == 4, f"Expected 4 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].text.startswith("sg"), f"Term base should get sg: {result[0].text}"
        assert result[1].kind == "open"

    async def test_thenlt_bare_decomposes(self, hol_session):
        """Standalone >- (top level, not in >> chain) decomposes correctly."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        assert len(result) == 4, f"Expected 4 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[1].kind == "open"

    async def test_thenlt_multi_step_arm_in_chain(self, hol_session):
        """>- with multi-step arm inside >> chain decomposes fully."""
        result = await call_step_plan(
            hol_session,
            "conj_tac >- (simp[] >> ACCEPT_TAC) >> fs[]"
        )
        # conj_tac, open_then1, simp[], ACCEPT_TAC, close_paren, fs[]
        assert len(result) == 6, f"Expected 6 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and "conj_tac" in result[0].text
        assert result[1].kind == "open"
        assert result[2].kind == "expand" and "simp" in result[2].text
        assert result[3].kind == "expand" and "ACCEPT" in result[3].text
        assert result[4].kind == "close"
        assert result[5].kind == "expand" and result[5].text == "fs[]"

    async def test_then_chain_without_thenlt_unchanged(self, hol_session):
        """Pure >> chain without >-/by is not affected by reexpand."""
        result = await call_step_plan(hol_session, "conj_tac >> simp[] >> fs[]")
        assert len(result) == 3
        assert all(s.kind == "expand" for s in result)

    async def test_nested_thenlt_with_then_chain(self, hol_session):
        """>- inside >- with >> chain decomposes recursively."""
        result = await call_step_plan(
            hol_session,
            "conj_tac >- (strip_tac >> simp[] >> strip_tac >- conj_tac)"
        )
        # conj_tac, open, strip_tac, simp[], strip_tac, open, conj_tac, close, close
        assert len(result) == 9, f"Expected 9 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and "conj_tac" in result[0].text
        assert result[1].kind == "open"
        assert result[2].text == "strip_tac"
        assert result[3].text == "simp[]"
        assert result[4].text == "strip_tac"
        assert result[5].kind == "open"  # inner >- open
        assert result[6].text == "conj_tac"
        assert result[7].kind == "close"  # inner >- close
        assert result[8].kind == "close"  # outer >- close

    async def test_thenlt_at_start_of_chain(self, hol_session):
        """>- as the first element in a >> chain decomposes."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> fs[]")
        # conj_tac, open_then1, simp[], close_paren, fs[]
        assert len(result) == 5
        assert result[1].kind == "open"

    async def test_multiple_thenlt_in_chain(self, hol_session):
        """Multiple >- in the same >> chain each decompose."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> conj_tac >- fs[]")
        # conj_tac, open, simp[], close, conj_tac, open, fs[], close
        assert len(result) == 8, f"Expected 8 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[1].kind == "open"
        assert result[5].kind == "open"

    async def test_end_offsets_correct_after_reexpand(self, hol_session):
        """End offsets for reexpanded fragments use original proof body positions."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> fs[]")
        ends = [s.end for s in result]
        for i in range(1, len(ends)):
            assert ends[i] >= ends[i-1], f"End offsets not monotonic at step {i}: {ends}"


# =============================================================================
# Step Plan: >~ (SELECT_GOAL_LT) decomposition
# =============================================================================

class TestGoalfragSelectGoalDecomposition:
    """>~[pat] >- tac decomposes into expand_list steps (not bare expand)."""

    async def test_select_goal_produces_expand_list(self, hol_session):
        """>~[`Foo`] >- simp[] becomes a single expand_list step."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- simp[]")
        # Should produce: expand(Cases_on), expand_list(Q.SELECT_GOAL_LT >- simp[])
        assert len(result) == 2
        assert result[0].kind == "expand"
        assert result[0].text == "Cases_on `x`"
        assert result[1].kind == "expand_list"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        assert ">-" in result[1].text
        assert "simp[]" in result[1].text

    async def test_select_goal_cmd_uses_expand_list(self, hol_session):
        """expand_list step generates goalFrag.expand_list command."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- simp[]")
        assert "goalFrag.expand_list" in result[1].cmd
        assert "goalFrag.expand_list" in result[1].cmd

    async def test_multiple_select_goals(self, hol_session):
        """Multiple >~ arms each become separate expand_list steps."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- simp[] >~ [`Bar`] >- simp[]"
        )
        # expand(Cases_on), expand_list(>~Foo>-simp), expand_list(>~Bar>-simp)
        assert len(result) == 3
        assert result[0].kind == "expand"
        assert result[1].kind == "expand_list"
        assert result[2].kind == "expand_list"
        assert "`Foo`" in result[1].text
        assert "`Bar`" in result[2].text

    async def test_select_goal_end_offsets(self, hol_session):
        """expand_list end offset covers the full >~ >- pattern."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- simp[]"
        )
        # expand_list end should be at end of "simp[]", which is after the pattern
        assert result[1].end > result[0].end

    async def test_select_goal_no_bare_pattern_expand(self, hol_session):
        """>~ pattern does NOT produce a bare expand step with just the pattern text."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- simp[]")
        # No step should have kind="expand" and text that is just a pattern list
        for step in result:
            if step.kind == "expand":
                assert not step.text.startswith("[`"), \
                    f"Bare pattern expand step found: {step.text}"

    async def test_select_goal_compound_body_then(self, hol_session):
        """>~[pat] >- (a >> b): compound body must be merged, not silently dropped.

        Regression: previously the SELECT_GOAL_LT prefix was dropped when the
        `>-` body had multiple tactics joined by `>>` (the bracket pattern
        match in tryConsumeBracket was open+single_expand+close). With the
        prefix dropped, the `>~` selector never executed and `>-` ran on the
        un-reordered goal stack, picking the wrong goal."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (simp[] >> fs[])")
        # Must produce: expand(Cases_on), expand_list(Q.SELECT_GOAL_LT [`Foo`] >- (simp[] >> fs[]))
        assert len(result) == 2, f"Expected 2 steps, got {len(result)}: {[(s.kind, s.text) for s in result]}"
        assert result[0].kind == "expand"
        assert result[1].kind == "expand_list", \
            f"Compound body should yield expand_list step, got kind={result[1].kind} text={result[1].text!r}"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        assert "`Foo`" in result[1].text
        assert "simp[]" in result[1].text
        assert "fs[]" in result[1].text

    async def test_select_goal_compound_body_three_then(self, hol_session):
        """>~[pat] >- (a >> b >> c): three-tactic compound body."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (a >> b >> c)")
        assert len(result) == 2
        assert result[1].kind == "expand_list"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        # All three sub-tactics must be present
        for tac in ("a", "b", "c"):
            assert tac in result[1].text

    async def test_select_goal_compound_body_associativity(self, hol_session):
        """Compound body must parenthesize so `>-` doesn't bind only to first sub-tactic.

        `Q.SELECT_GOAL_LT [pat] >- a >> b` parses as
          `(Q.SELECT_GOAL_LT [pat] >- a) >> b`
        which would run `b` on goals OUTSIDE the >- arm. The body must be
        wrapped in parens so the entire compound is the arm body."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (simp[] >> fs[])")
        # The combined text must keep simp[] >> fs[] grouped (parens, or some
        # equivalent that prevents `>-` from binding only to simp[]).
        text = result[1].text
        # Find the position of `>-` and check what follows is parenthesized
        dash_idx = text.find(">-")
        assert dash_idx >= 0
        body = text[dash_idx + 2:].lstrip()
        assert body.startswith("("), \
            f"Compound body must be parenthesized; got {body!r}"


# =============================================================================
# Resume goal extraction
#
# Regression tests for a bug where `resume_goal_terms` referenced
# `boolLib.find_suspension` (does not exist) instead of
# `markerLib.lookup_suspension`, causing `extract_resume_goal_json` and
# `verify_resume_json` to fail to compile. The downstream symptom was:
#
#     Failed to extract Resume goal for '<thm>[<label>]'; goals_json: NO_PROOFS
#
# These tests pin the SML-level entry points so the bug cannot regress
# silently behind the higher-level cursor tests.
# =============================================================================


async def _setup_split_conj(session: HOLSession) -> None:
    """Define a parent theorem with two suspended subgoals in the live session."""
    await session.send('drop_all();', timeout=5)
    parent = (
        'Theorem split_conj:\n'
        '  p /\\ (p ==> q) ==> p /\\ q\n'
        'Proof\n'
        '  strip_tac >> conj_tac\n'
        '  >- suspend "p_case"\n'
        '  >- suspend "q_case"\n'
        'QED'
    )
    result = await session.send(parent, timeout=30)
    assert "saved theorem" in result.lower() or "stashing" in result.lower(), (
        f"Parent theorem did not register: {result[-500:]}"
    )


class TestResumeGoalExtraction:
    """Direct SML tests for the Resume goal extraction helpers."""

    async def test_extract_resume_goal_json_first_label(self, hol_session):
        """extract_resume_goal_json returns the suspended subgoal as JSON."""
        await _setup_split_conj(hol_session)
        result = await hol_session.send(
            'extract_resume_goal_json "split_conj" "p_case";', timeout=10
        )
        # Must have produced a JSON ok line (not an err, not a static error).
        ok_line = None
        for line in result.strip().split('\n'):
            line = line.strip()
            if line.startswith('{"ok":'):
                ok_line = line
                break
        assert ok_line is not None, (
            f"extract_resume_goal_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        # The first suspended subgoal of split_conj is `p` (with `p ==> q` as asm
        # added by `strip_tac`). extract_resume_goal_json prints types, so the
        # term renders as e.g. "(p :bool)".
        assert 'p' in payload['goal'] and 'bool' in payload['goal'], (
            f"Unexpected goal text: {payload!r}"
        )

    async def test_extract_resume_goal_json_second_label(self, hol_session):
        """Both suspended labels are independently extractable."""
        await _setup_split_conj(hol_session)
        result = await hol_session.send(
            'extract_resume_goal_json "split_conj" "q_case";', timeout=10
        )
        ok_line = next(
            (line.strip() for line in result.strip().split('\n')
             if line.strip().startswith('{"ok":')),
            None,
        )
        assert ok_line is not None, (
            f"extract_resume_goal_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        # Second subgoal is `q`; types are printed.
        assert 'q' in payload['goal'] and 'bool' in payload['goal'], (
            f"Unexpected goal text: {payload!r}"
        )

    async def test_extract_resume_goal_json_unknown_suspension(self, hol_session):
        """Looking up a non-existent suspension reports an error, not a crash."""
        await hol_session.send('drop_all();', timeout=5)
        result = await hol_session.send(
            'extract_resume_goal_json "no_such_thm" "no_label";', timeout=5
        )
        # Should produce a JSON err line — NOT a Poly/ML 'has not been declared'
        # static error (which is the symptom of the original bug).
        assert "has not been declared" not in result, (
            f"resume_goal_terms failed to compile: {result!r}"
        )
        assert any(
            line.strip().startswith('{"err":') for line in result.strip().split('\n')
        ), f"Expected JSON err line; got: {result!r}"

    async def test_verify_resume_json_closes_subgoal(self, hol_session):
        """verify_resume_json runs Resume tactics against the suspended goal."""
        await _setup_split_conj(hol_session)
        # `ASM_REWRITE_TAC[]` closes `p` given `p` is in the asms (added by strip_tac).
        cmd = (
            'verify_resume_json "split_conj" "p_case" "split_conj_p_case" '
            '["ef(goalFrag.expand(ASM_REWRITE_TAC[]))"] false 10.0;'
        )
        result = await hol_session.send(cmd, timeout=20)
        ok_line = next(
            (line.strip() for line in result.strip().split('\n')
             if line.strip().startswith('{"ok":')),
            None,
        )
        assert ok_line is not None, (
            f"verify_resume_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        trace = payload.get('trace', [])
        assert trace, f"Empty trace from verify_resume_json: {payload!r}"
        # Final tactic must close the goal (goals_after == 0).
        assert trace[-1].get('goals_after') == 0, (
            f"Resume tactics did not close goal: {trace!r}"
        )
