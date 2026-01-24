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
        
        for text, start, end in result:
            # Extract from original using span
            extracted = tactic[start:end]
            # Should match the text (allowing for whitespace trimming)
            assert text.strip() in extracted or extracted in text

    async def test_spans_non_overlapping(self, hol_session):
        """Spans should not overlap."""
        tactic = "a >- b >- c >- d"
        result = await call_linearize(hol_session, tactic)
        
        # Sort by start position
        sorted_result = sorted(result, key=lambda x: x[1])
        
        # Check no overlaps
        for i in range(len(sorted_result) - 1):
            _, _, end1 = sorted_result[i]
            _, start2, _ = sorted_result[i + 1]
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
