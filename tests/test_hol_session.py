"""Tests for HOL session subprocess wrapper."""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_cursor import _is_hol_error

FIXTURES_DIR = Path(__file__).parent / "fixtures"


async def test_hol_session():
    """Test HOL session basic functionality."""
    session = HOLSession(str(FIXTURES_DIR))
    try:
        result = await session.start()
        assert "HOL started" in result

        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result

        assert session.is_running
    finally:
        await session.stop()
        assert not session.is_running


async def test_hol_session_context_manager():
    """Test HOL session as async context manager."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        assert session.is_running
        result = await session.send('3 + 4;', timeout=10)
        assert "7" in result
        assert session.is_running
    assert not session.is_running


async def test_hol_session_interrupt():
    """Test interrupting a long-running HOL command."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Start a long-running computation via short timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should still be usable after interrupt
        assert session.is_running
        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result


async def test_hol_session_send_not_running():
    """Test sending to a stopped session returns error."""
    session = HOLSession(str(FIXTURES_DIR))
    result = await session.send('1 + 1;', timeout=10)
    assert "ERROR" in result


async def test_hol_session_start_already_running():
    async with HOLSession(str(FIXTURES_DIR)) as session:
        pid = session.process.pid
        result = await session.start()
        assert "already running" in result.lower()
        assert session.process.pid == pid


async def test_hol_session_sequential_sends():
    """Test sequential sends return correct outputs in order."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        for i in range(10):
            result = await session.send(f'{i};', timeout=10)
            assert str(i) in result, f"Expected {i} in result, got: {result}"


async def test_hol_session_post_interrupt_sync():
    """Test that session resyncs correctly after interrupt.

    After timeout/interrupt, buffer and pipe may have stale data.
    Verify subsequent commands work correctly.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Trigger interrupt with a timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should resync - send a few commands and verify correct outputs
        for i in range(5):
            result = await session.send(f'{100 + i};', timeout=10)
            assert str(100 + i) in result, f"Expected {100+i} after interrupt, got: {result}"


# Unit tests for escape_sml_string

def test_escape_sml_string_backslash():
    """Backslash should be doubled for SML string literal."""
    assert escape_sml_string('/\\') == '/\\\\'
    assert escape_sml_string('A /\\ B') == 'A /\\\\ B'


def test_escape_sml_string_quote():
    """Double quotes should be escaped."""
    assert escape_sml_string('SPEC "x"') == 'SPEC \\"x\\"'


def test_escape_sml_string_newline():
    """Newlines should become \\n."""
    assert escape_sml_string('foo\nbar') == 'foo\\nbar'


def test_escape_sml_string_tab():
    """Tabs should become \\t."""
    assert escape_sml_string('foo\tbar') == 'foo\\tbar'


def test_escape_sml_string_carriage_return():
    """Carriage returns should become \\r."""
    assert escape_sml_string('foo\rbar') == 'foo\\rbar'


def test_escape_sml_string_combined():
    """Test multiple escape sequences together."""
    # /\ with newline and embedded quote
    assert escape_sml_string('`T /\\ T`\nby SPEC "x"') == '`T /\\\\ T`\\nby SPEC \\"x\\"'


def test_escape_sml_string_no_change():
    """Regular strings pass through unchanged."""
    assert escape_sml_string('simp[]') == 'simp[]'
    assert escape_sml_string('strip_tac') == 'strip_tac'


# Tests for _is_hol_error with real HOL output

async def test_is_hol_error_detects_syntax_error():
    """Poly/ML syntax errors should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('val x = ;', timeout=10)  # syntax error
        assert _is_hol_error(result), f"Should detect syntax error: {result}"


async def test_is_hol_error_detects_type_error():
    """Poly/ML type errors should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('val x : int = "hello";', timeout=10)
        assert _is_hol_error(result), f"Should detect type error: {result}"


async def test_is_hol_error_detects_exception():
    """SML exceptions should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('raise Fail "test";', timeout=10)
        assert _is_hol_error(result), f"Should detect exception: {result}"


async def test_is_hol_error_ignores_error_in_term():
    """The word 'error' in a term should NOT trigger error detection."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Define a value with "error" in the name - this is valid SML
        result = await session.send('val error_state = 42;', timeout=10)
        assert not _is_hol_error(result), f"Should not flag 'error' in identifier: {result}"

        # Use "error" in a HOL term
        result = await session.send('val t = ``is_error x``;', timeout=10)
        assert not _is_hol_error(result), f"Should not flag 'error' in term: {result}"


def test_is_hol_error_detects_timeout():
    """_is_hol_error catches TIMEOUT strings from send()."""
    assert _is_hol_error("TIMEOUT after 30s - sent interrupt.")
    assert _is_hol_error("TIMEOUT after 5s - sent interrupt.\npartial output")


def test_is_hol_error_detects_error_prefix():
    """_is_hol_error catches ERROR: sentinel outputs."""
    assert _is_hol_error("ERROR: HOL not running")
    assert _is_hol_error("Error: HOL not running")
