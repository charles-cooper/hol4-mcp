"""Tests for HOL file parser."""

import pytest
from pathlib import Path

from hol4_mcp.hol_file_parser import (
    parse_theorems, parse_file, splice_into_theorem, parse_p_output,
)

FIXTURES_DIR = Path(__file__).parent / "fixtures"


def test_parse_theorems():
    """Test parsing theorems from content."""
    content = r'''
Theorem foo[simp]:
  !x. P x ==> Q x
Proof
  rw[] \\
  cheat
QED

Triviality bar:
  A /\ B ==> B /\ A
Proof
  metis_tac[]
QED

Theorem baz[local,simp]:
  !n. n + 0 = n
Proof
  Induct_on `n` \\
  gvs[] \\
  cheat
QED
'''
    thms = parse_theorems(content)

    assert len(thms) == 3

    assert thms[0].name == "foo"
    assert thms[0].kind == "Theorem"
    assert thms[0].has_cheat == True
    assert thms[0].attributes == ["simp"]
    assert "rw[]" in thms[0].proof_body

    assert thms[1].name == "bar"
    assert thms[1].kind == "Triviality"
    assert thms[1].has_cheat == False

    assert thms[2].name == "baz"
    assert thms[2].attributes == ["local", "simp"]
    assert thms[2].has_cheat == True


def test_parse_fixture_file():
    """Test parsing the fixture HOL file."""
    f = FIXTURES_DIR / "testScript.sml"
    if not f.exists():
        pytest.skip(f"Fixture not found: {f}")

    thms = parse_file(f)
    assert len(thms) == 5

    assert thms[0].name == "add_zero"
    assert thms[0].has_cheat == False

    assert thms[1].name == "needs_proof"
    assert thms[1].has_cheat == True

    assert thms[2].name == "partial_proof"
    assert thms[2].has_cheat == True
    assert thms[2].proof_body  # has content before cheat

    assert thms[4].name == "helper_lemma"
    assert thms[4].kind == "Triviality"


def test_splice_into_theorem():
    """Test splicing proof into theorem."""
    content = '''Theorem foo:
  !x. P x
Proof
  cheat
QED

Theorem bar:
  A
Proof
  simp[]
QED
'''
    new = splice_into_theorem(content, 'foo', 'Induct_on `x` \\\\ gvs[]')

    assert 'Induct_on `x`' in new
    assert 'cheat' not in new.split('Theorem bar')[0]
    assert 'simp[]' in new


def test_parse_p_output():
    """Test parsing p() output."""
    output = '''> p();
Induct_on `x` \\
gvs[] \\
simp[foo_def]
val it = () : unit
'''
    result = parse_p_output(output)
    assert result == '''Induct_on `x` \\
gvs[] \\
simp[foo_def]'''


def test_splice_into_theorem_not_found():
    content = 'Theorem foo:\n  P\nProof\n  cheat\nQED\n'
    with pytest.raises(ValueError, match="not found"):
        splice_into_theorem(content, 'nonexistent', 'simp[]')


def test_parse_p_output_empty():
    assert parse_p_output("") is None


def test_parse_p_output_only_prompts():
    assert parse_p_output("> p();\nval it = () : unit\n") is None


def test_parse_p_output_error():
    """Error output should return None, not be spliced as tactics."""
    error_output = """No goalstack is currently being managed.
Exception- HOL_ERR at proofManagerLib.p: raised"""
    assert parse_p_output(error_output) is None


def test_parse_p_output_error_prefix():
    """ERROR: sentinel outputs should return None."""
    assert parse_p_output("ERROR: HOL not running") is None
    assert parse_p_output("Error: HOL not running") is None


def test_parse_p_output_multiline_val_it():
    """Regression: multi-line 'val it =' format was returning None."""
    # Format 3: val it = on its own line, tactic on subsequent lines
    output = '''\
val it =
   completeInduct_on `LENGTH xs` \\
    rw[LET_THM] \\
     Cases_on `n >= LENGTH xs`
      >- (simp[])
      >- (gvs[])
: proof'''
    result = parse_p_output(output)
    assert result is not None, "Should parse multi-line val it format"
    assert 'completeInduct_on' in result
    assert ': proof' not in result  # Type annotation stripped
    assert 'val it' not in result   # val binding stripped


def test_parse_p_output_multiline_val_it_inline_proof():
    """Multi-line val it with : proof on last content line."""
    output = '''\
val it =
   simp[] \\
    gvs[]: proof'''
    result = parse_p_output(output)
    assert result is not None
    assert result.strip().endswith('gvs[]')
    assert ': proof' not in result
