"""Tests for linearize_with_spans SML function.

This tests the tactic linearization used by FileProofCursor for mapping
file positions to proof state.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_linearize_with_spans_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with cheat_finder loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    # Load the cheat_finder.sml which defines linearize_with_spans
    result = await session.send(f'use "{SML_HELPERS_DIR / "cheat_finder.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load cheat_finder.sml: {result}"
    yield session
    await session.stop()


async def call_linearize(session: HOLSession, tactic_str: str) -> list[tuple[str, int, int]]:
    """Call linearize_with_spans and parse the result."""
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'linearize_with_spans_json "{escaped}";', timeout=10)
    return parse_linearize_with_spans_output(result)


class TestLinearizeBasic:
    """Basic linearization tests."""

    async def test_single_tactic(self, hol_session):
        """Single tactic should return one item."""
        result = await call_linearize(hol_session, "simp[]")
        assert len(result) == 1
        assert result[0][0] == "simp[]"

    async def test_then_chain(self, hol_session):
        """>> chain should be kept together."""
        result = await call_linearize(hol_session, "rpt strip_tac >> simp[] >> fs[]")
        # All in one chain
        assert len(result) >= 1
        # Should contain all parts
        full_text = " ".join(r[0] for r in result)
        assert "strip_tac" in full_text
        assert "simp[]" in full_text
        assert "fs[]" in full_text

    async def test_thenlt_split(self, hol_session):
        """Basic >- should split into separate arms."""
        result = await call_linearize(hol_session, "conj_tac >- simp[] >- fs[]")
        assert len(result) >= 3
        texts = [r[0] for r in result]
        assert any("conj_tac" in t for t in texts)
        assert any("simp[]" in t for t in texts)
        assert any("fs[]" in t for t in texts)

    async def test_empty_string(self, hol_session):
        """Empty string should return empty list."""
        result = await call_linearize(hol_session, "")
        assert result == []


class TestLinearizeByConstruct:
    """Tests for `by` and `suffices_by` constructs."""

    async def test_by_tactic(self, hol_session):
        """`X by tac` should be kept as atomic unit."""
        result = await call_linearize(hol_session, "`foo` by simp[]")
        assert len(result) == 1
        assert "by" in result[0][0]
        assert "simp[]" in result[0][0]

    async def test_suffices_by_tactic(self, hol_session):
        """`suffices_by` should be kept as atomic unit."""
        result = await call_linearize(hol_session, "`foo` suffices_by simp[]")
        assert len(result) == 1
        assert "suffices_by" in result[0][0]

    async def test_by_in_chain(self, hol_session):
        """`by` in >> chain should be atomic."""
        result = await call_linearize(hol_session, "rpt strip_tac >> `P x` by simp[] >> fs[]")
        # Should have multiple items but `by` should be atomic
        by_items = [r for r in result if "by" in r[0]]
        assert len(by_items) >= 1
        # The `by` item should contain both the goal and tactic
        assert any("`P x`" in r[0] and "simp[]" in r[0] for r in by_items)

    async def test_by_span_offset_not_zero(self, hol_session):
        """`by` construct mid-proof should have correct span offset, not 0.

        Regression test for Bug 1: node_span didn't handle TacticParse.Subgoal,
        causing `by` constructs to have start offset 0 (incorrectly including
        all preceding tactics in the span text).
        """
        tactic = "rpt strip_tac >> `P x` by simp[]"
        result = await call_linearize(hol_session, tactic)

        # Find the `by` item
        by_items = [r for r in result if "by" in r[0]]
        assert len(by_items) == 1

        text, start, end, use_eall = by_items[0]

        # The `by` construct should NOT start at 0 - it comes after "rpt strip_tac >> "
        assert start > 0, f"`by` construct should not start at offset 0, got start={start}"

        # Verify the span text matches what we extract from the original
        extracted = tactic[start:end]
        assert "`P x`" in extracted
        assert "simp[]" in extracted
        # Should NOT include the earlier tactics
        assert "rpt" not in extracted
        assert "strip_tac" not in text  # The returned text should only be the `by` construct


class TestLinearizeThenInThenLT:
    """Tests for Then nodes inside ThenLT - the bug that was fixed."""

    async def test_then_inside_thenlt_simple(self, hol_session):
        """Then chain followed by >- arm should work.
        
        This was the bug: `rpt strip_tac >> foo[] >- (bar[])` would return []
        because Then nodes inside ThenLT weren't handled by flatten_split_spans.
        """
        result = await call_linearize(hol_session, "rpt strip_tac >> foo[] >- (bar[])")
        assert len(result) >= 2
        texts = [r[0] for r in result]
        assert any("strip_tac" in t for t in texts)
        assert any("bar[]" in t for t in texts)

    async def test_then_inside_thenlt_with_parens(self, hol_session):
        """Parenthesized >- arm at end should work."""
        result = await call_linearize(hol_session, "conj_tac >- simp[] >- (fs[] >> gvs[])")
        assert len(result) >= 3
        texts = [r[0] for r in result]
        assert any("conj_tac" in t for t in texts)
        assert any("simp[]" in t for t in texts)
        # The parenthesized chain should be present
        assert any("fs[]" in t or "gvs[]" in t for t in texts)

    async def test_nested_thenlt_with_then(self, hol_session):
        """Deeply nested ThenLT with Then chains should work."""
        tactic = "a >> b >- (c >> d >- e >- f) >- (g >> h)"
        result = await call_linearize(hol_session, tactic)
        assert len(result) >= 4
        texts = [r[0] for r in result]
        # All major components should be present
        for letter in "abcdefgh":
            assert any(letter in t for t in texts), f"Missing '{letter}' in {texts}"

    async def test_complete_proof_pattern(self, hol_session):
        """Pattern that matches the original failing case."""
        # This mimics the structure of the transfer_sub_add_preserves_sum proof
        tactic = """rpt strip_tac
  >> `P x` by simp[]
  >> `Q y` by fs[]
  >> Cases_on `cond`
  >- (imp_res_tac foo >> simp[])
  >- (imp_res_tac bar >> simp[])"""
        result = await call_linearize(hol_session, tactic)
        assert len(result) >= 5
        texts = [r[0] for r in result]
        assert any("strip_tac" in t for t in texts)
        assert any("Cases_on" in t for t in texts)
        assert any("foo" in t for t in texts)
        assert any("bar" in t for t in texts)


class TestLinearizeWrapperPreservation:
    """Tests for preserving tactic wrappers like rpt, TRY, REPEAT.
    
    Regression tests for bug where `rpt strip_tac >> sg `foo` >- simp[]`
    would lose the `rpt` prefix, returning ('strip_tac', 4, 13) instead
    of ('rpt strip_tac', 0, 13).
    """

    async def test_rpt_preserved_simple(self, hol_session):
        """rpt should be preserved in simple case."""
        result = await call_linearize(hol_session, "rpt strip_tac")
        assert len(result) == 1
        assert result[0][0] == "rpt strip_tac"
        assert result[0][1] == 0  # Should start at offset 0

    async def test_rpt_preserved_in_chain(self, hol_session):
        """rpt should be preserved in >> chain."""
        result = await call_linearize(hol_session, "rpt strip_tac >> simp[]")
        assert len(result) == 2
        assert result[0][0] == "rpt strip_tac"
        assert result[0][1] == 0

    async def test_rpt_preserved_with_sg_split(self, hol_session):
        """rpt should be preserved when followed by sg >- (the original bug).
        
        This was the exact pattern that failed: when a >> chain containing
        rpt is followed by sg `...` >-, the rpt wrapper was being stripped.
        """
        result = await call_linearize(hol_session, "rpt strip_tac >> sg `foo` >- simp[]")
        assert len(result) >= 2
        # First tactic should be the full rpt strip_tac, not just strip_tac
        assert result[0][0] == "rpt strip_tac"
        assert result[0][1] == 0  # Must start at offset 0, not 4

    async def test_try_preserved(self, hol_session):
        """TRY should be preserved."""
        result = await call_linearize(hol_session, "TRY simp[] >> fs[]")
        assert len(result) == 2
        assert result[0][0] == "TRY simp[]"
        assert result[0][1] == 0

    async def test_repeat_preserved(self, hol_session):
        """REPEAT should be preserved."""
        result = await call_linearize(hol_session, "REPEAT strip_tac >> simp[]")
        assert len(result) == 2
        assert result[0][0] == "REPEAT strip_tac"
        assert result[0][1] == 0

    async def test_nested_wrappers_preserved(self, hol_session):
        """Nested wrappers like TRY (rpt ...) should be preserved."""
        result = await call_linearize(hol_session, "TRY (rpt strip_tac) >> simp[]")
        assert len(result) == 2
        assert result[0][0] == "TRY (rpt strip_tac)"
        assert result[0][1] == 0


class TestLinearizeSpans:
    """Tests for span (start, end) positions."""

    async def test_span_positions_correct(self, hol_session):
        """Span positions should match actual text positions."""
        tactic = "simp[] >> fs[]"
        result = await call_linearize(hol_session, tactic)
        
        for item in result:
            text, start, end = item[0], item[1], item[2]
            # Extract from original using span
            extracted = tactic[start:end]
            # Should match the text (allowing for whitespace trimming)
            assert text.strip() in extracted or extracted in text

    async def test_spans_non_overlapping(self, hol_session):
        """Spans should not overlap."""
        tactic = "a >- b >- c >- d"
        result = await call_linearize(hol_session, tactic)
        
        # Sort by start position (item[1] is start offset)
        sorted_result = sorted(result, key=lambda x: x[1])
        
        # Check no overlaps
        for i in range(len(sorted_result) - 1):
            end1 = sorted_result[i][2]
            start2 = sorted_result[i + 1][1]
            assert end1 <= start2, f"Overlap: item {i} ends at {end1}, item {i+1} starts at {start2}"


class TestLinearizeEdgeCases:
    """Edge cases and special patterns."""

    async def test_cheat_tactic(self, hol_session):
        """cheat should be recognized."""
        result = await call_linearize(hol_session, "simp[] >> cheat")
        assert any("cheat" in r[0] for r in result)

    async def test_sg_tactic(self, hol_session):
        """sg (subgoal) should work."""
        result = await call_linearize(hol_session, "sg `P x` >- simp[]")
        assert len(result) >= 2

    async def test_first_tactic(self, hol_session):
        """FIRST combinator should work."""
        result = await call_linearize(hol_session, "FIRST [simp[], fs[], gvs[]]")
        assert len(result) >= 1

    async def test_try_tactic(self, hol_session):
        """TRY combinator should work."""
        result = await call_linearize(hol_session, "TRY simp[]")
        assert len(result) >= 1

    async def test_repeat_tactic(self, hol_session):
        """REPEAT combinator should work."""
        result = await call_linearize(hol_session, "REPEAT strip_tac")
        assert len(result) >= 1

    async def test_quoted_term_with_special_chars(self, hol_session):
        """Quoted terms with special characters should work."""
        result = await call_linearize(hol_session, r"`!x. P x ==> Q x` by simp[]")
        assert len(result) == 1
        assert "==>" in result[0][0]

    async def test_multiline_tactic(self, hol_session):
        """Multi-line tactics should work."""
        tactic = "rpt strip_tac\n  >> simp[]\n  >> fs[]"
        result = await call_linearize(hol_session, tactic)
        assert len(result) >= 1
        # Should handle newlines in the string
        full_text = " ".join(r[0] for r in result)
        assert "strip_tac" in full_text


class TestLinearizeLongProofs:
    """Tests with longer/more realistic proofs."""

    async def test_proof_with_many_tactics(self, hol_session):
        """Proof with many tactics should not return empty."""
        # Build a long proof-like string
        tactics = ["rpt strip_tac"]
        for i in range(20):
            tactics.append(f"  >> `P{i} x` by simp[]")
        tactics.append("  >> cheat")
        tactic = "\n".join(tactics)
        
        result = await call_linearize(hol_session, tactic)
        assert len(result) >= 20, f"Expected >= 20 items, got {len(result)}"

    async def test_proof_with_nested_cases(self, hol_session):
        """Proof with nested Cases_on patterns."""
        tactic = """Cases_on `x`
  >- (Cases_on `y` >- simp[] >- fs[])
  >- (Cases_on `z` >- gvs[] >- metis_tac[])"""
        result = await call_linearize(hol_session, tactic)
        assert len(result) >= 5
        texts = [r[0] for r in result]
        # Should have all the Cases_on
        assert sum(1 for t in texts if "Cases_on" in t) >= 3


class TestUseEallFlag:
    """Tests for the use_eall flag (4th element) which indicates >> chain membership."""

    async def test_single_tactic_no_eall(self, hol_session):
        """Single tactic should have use_eall=False."""
        result = await call_linearize(hol_session, "simp[]")
        assert len(result) == 1
        text, start, end, use_eall = result[0]
        assert use_eall is False

    async def test_then_chain_first_no_eall(self, hol_session):
        """First tactic in >> chain should have use_eall=False."""
        result = await call_linearize(hol_session, "simp[] >> gvs[]")
        assert len(result) == 2
        text1, start1, end1, use_eall1 = result[0]
        assert "simp" in text1
        assert use_eall1 is False

    async def test_then_chain_subsequent_eall(self, hol_session):
        """Subsequent tactics in >> chain should have use_eall=True."""
        result = await call_linearize(hol_session, "simp[] >> gvs[] >> rw[]")
        assert len(result) == 3
        # First: use_eall=False
        assert result[0][3] is False
        # Second: use_eall=True
        assert result[1][3] is True
        # Third: use_eall=True
        assert result[2][3] is True

    async def test_thenl_arms_reset_eall(self, hol_session):
        """Each >- arm should start with use_eall=False."""
        result = await call_linearize(hol_session, "a >- b >- c")
        # Each arm is independent, all should be use_eall=False
        assert len(result) == 3
        for item in result:
            assert item[3] is False, f"Expected use_eall=False for {item[0]}"

    async def test_then_inside_thenl_arm(self, hol_session):
        """>> chain inside >- arm: parenthesized groups stay atomic."""
        result = await call_linearize(hol_session, "a >- (b >> c >> d)")
        # Parenthesized groups are kept atomic, so:
        # a: use_eall=False (base)
        # (b >> c >> d): use_eall=False (atomic group in arm)
        assert len(result) == 2
        assert result[0][0] == "a"
        assert result[0][3] is False
        assert "(b >> c >> d)" in result[1][0]
        assert result[1][3] is False

    async def test_unparensed_then_inside_thenl_arm(self, hol_session):
        """>> chain inside >- arm without parens: gets split with eall flags."""
        # Without parens at top level of arm, the >> chain gets split
        result = await call_linearize(hol_session, "a >- b >> c >> d")
        # This parses as: a >- ((b >> c) >> d), so arm has >> chain
        # But actually ThenLT flattens, so we get: base=a, arm=[b >> c >> d]
        # The arm's >> chain gets split:
        # a: use_eall=False (base)
        # b: use_eall=False (first in arm's >> chain)
        # c: use_eall=True
        # d: use_eall=True
        assert len(result) >= 3
        # First should be a
        assert result[0][3] is False

    async def test_thenl_after_then(self, hol_session):
        """>- structure after >>: base gets use_eall=true, arms stay false.

        Regression test for Bug 2: flatten_then_chain was forcing use_eall=true
        on ALL spans from rest items, including >- arm spans which should stay false.
        """
        result = await call_linearize(hol_session, "a >> (b >- c >- d)")
        # Expected:
        # a: use_eall=False (first in >> chain)
        # b: use_eall=True (base of >- structure, after >>)
        # c: use_eall=False (>- arm)
        # d: use_eall=False (>- arm)
        assert len(result) == 4
        texts = [r[0] for r in result]
        ealls = [r[3] for r in result]

        assert "a" in texts[0]
        assert ealls[0] is False, "First item in >> chain should have use_eall=False"

        assert "b" in texts[1]
        assert ealls[1] is True, "Base of >- after >> should have use_eall=True"

        assert "c" in texts[2]
        assert ealls[2] is False, ">- arm should have use_eall=False"

        assert "d" in texts[3]
        assert ealls[3] is False, ">- arm should have use_eall=False"

    async def test_complex_chain(self, hol_session):
        """Complex pattern: a >> b >- (c >> d) >- e."""
        result = await call_linearize(hol_session, "a >> b >- (c >> d) >- e")
        # Parenthesized (c >> d) is kept atomic. Expected:
        # a: use_eall=False (first in base >> chain)
        # b: use_eall=True (second in base >> chain)
        # (c >> d): use_eall=False (atomic group in arm)
        # e: use_eall=False (single tactic in arm)
        texts = [r[0] for r in result]
        ealls = [r[3] for r in result]
        
        assert len(result) == 4
        # a is first in base chain
        assert ealls[0] is False
        # b follows a in >> chain
        assert ealls[1] is True
        # (c >> d) is atomic group
        assert ealls[2] is False
        # e is alone in its arm
        assert ealls[3] is False
