"""Parse HOL4 script files for theorem structure."""

import bisect
import re
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class TacticSpan:
    """A tactic with its source position."""
    text: str
    start: tuple[int, int]  # (line, col), 1-indexed
    end: tuple[int, int]    # (line, col), 1-indexed


def build_line_starts(content: str) -> list[int]:
    """Build table mapping line numbers to char offsets.

    line_starts[i] = char offset where line (i+1) begins.
    Line numbers are 1-indexed, but array is 0-indexed.
    """
    starts = [0]  # Line 1 starts at offset 0
    for i, c in enumerate(content):
        if c == '\n':
            starts.append(i + 1)  # Next line starts after newline
    return starts


def offset_to_line_col(offset: int, line_starts: list[int]) -> tuple[int, int]:
    """Convert char offset to (line, col), both 1-indexed."""
    # Find the line: largest line_starts[i] <= offset
    line = bisect.bisect_right(line_starts, offset)
    col = offset - line_starts[line - 1] + 1
    return (line, col)


def line_col_to_offset(line: int, col: int, line_starts: list[int]) -> int:
    """Convert (line, col) to char offset. Line and col are 1-indexed."""
    if line < 1 or line > len(line_starts):
        raise ValueError(f"Line {line} out of range (1-{len(line_starts)})")
    return line_starts[line - 1] + col - 1


def parse_linearize_with_spans_output(output: str) -> list[tuple[str, int, int]]:
    """Parse JSON output from linearize_with_spans_json.

    Expects: {"ok":[{"t":"text","s":0,"e":8},...]} or {"err":"message"}
    Returns: list of (text, start_offset, end_offset) tuples.
    """
    import json
    import logging

    try:
        result = json.loads(output.strip().split('\n')[0])
        if 'ok' in result:
            return [(item['t'], item['s'], item['e']) for item in result['ok']]
        elif 'err' in result:
            logging.warning(f"linearize_with_spans_json error: {result['err']}")
            return []
        else:
            return []
    except (ValueError, json.JSONDecodeError, KeyError) as e:
        logging.warning(f"Failed to parse linearize_with_spans_json: {e}")
        return []


def make_tactic_spans(
    raw_spans: list[tuple[str, int, int]],
    proof_body_offset: int,
    line_starts: list[int],
) -> list[TacticSpan]:
    """Convert raw (text, start, end) tuples to TacticSpan with line/col.

    Args:
        raw_spans: Output from parse_linearize_with_spans_output (offsets relative to proof body)
        proof_body_offset: Char offset where proof body starts in the file
        line_starts: Line start table for the entire file

    Returns:
        List of TacticSpan with absolute line/col positions in the file.
    """
    result = []
    for text, start, end in raw_spans:
        # Convert relative offsets to absolute
        abs_start = proof_body_offset + start
        abs_end = proof_body_offset + end
        start_lc = offset_to_line_col(abs_start, line_starts)
        end_lc = offset_to_line_col(abs_end, line_starts)
        result.append(TacticSpan(text=text, start=start_lc, end=end_lc))
    return result


@dataclass
class TheoremInfo:
    """Information about a theorem in a HOL script file."""
    name: str
    kind: str  # "Theorem" or "Triviality"
    goal: str  # The statement to prove
    start_line: int  # Line of "Theorem name:"
    proof_start_line: int  # Line after "Proof" (first line of proof body)
    proof_end_line: int  # Line after "QED" (first line after theorem)
    has_cheat: bool
    proof_body: str = ""  # Content between Proof and QED
    attributes: list[str] = field(default_factory=list)

    @property
    def line_before_qed(self) -> int:
        """Line number of QED - 1 (last line of proof body)."""
        return self.proof_end_line - 2


def parse_theorems(content: str) -> list[TheoremInfo]:
    """Parse .sml file content, return all theorems in order."""
    theorems = []
    lines = content.split('\n')

    # Pattern for Theorem/Triviality with optional attributes
    # Matches: Theorem name:, Theorem name[simp]:, Triviality foo[local,simp]:
    header_pattern = re.compile(
        r'^(Theorem|Triviality)\s+(\w+)(?:\s*\[([^\]]*)\])?\s*:',
        re.MULTILINE
    )

    for match in header_pattern.finditer(content):
        kind = match.group(1)
        name = match.group(2)
        attrs_str = match.group(3)
        attributes = [a.strip() for a in attrs_str.split(',')] if attrs_str else []

        # Find line number of header
        start_pos = match.start()
        start_line = content[:start_pos].count('\n') + 1

        # Find Proof and QED after this point
        rest = content[match.end():]

        proof_match = re.search(r'^\s*Proof\s*$', rest, re.MULTILINE)
        if not proof_match:
            continue

        qed_match = re.search(r'^\s*QED\s*$', rest, re.MULTILINE)
        if not qed_match:
            continue

        # Extract goal (between : and Proof)
        goal = rest[:proof_match.start()].strip()

        # Calculate line numbers
        proof_start_line = start_line + rest[:proof_match.start()].count('\n') + 1
        proof_end_line = start_line + rest[:qed_match.start()].count('\n') + 1

        # Extract proof body
        proof_body = rest[proof_match.end():qed_match.start()]

        # Check for cheat
        has_cheat = bool(re.search(r'\bcheat\b', proof_body, re.IGNORECASE))

        theorems.append(TheoremInfo(
            name=name,
            kind=kind,
            goal=goal,
            start_line=start_line,
            proof_start_line=proof_start_line,
            proof_end_line=proof_end_line,
            has_cheat=has_cheat,
            proof_body=proof_body.strip(),
            attributes=attributes,
        ))

    return theorems


def parse_file(path: Path) -> list[TheoremInfo]:
    """Parse .sml file, return all theorems."""
    content = path.read_text()
    return parse_theorems(content)


def splice_into_theorem(content: str, name: str, tactics: str) -> str:
    """Replace Proof...QED block for named theorem with new tactics.

    Raises:
        ValueError: If theorem not found in content.
    """
    # Match Theorem/Triviality name[...]: ... Proof ... QED
    pattern = rf'''
        ((?:Theorem|Triviality)\s+{re.escape(name)}
         (?:\s*\[[^\]]*\])?    # optional attributes
         \s*:\s*
         .*?                   # goal (non-greedy)
         \n\s*Proof\s*\n)      # Proof line
        (.*?)                  # old tactics
        (\n\s*QED)             # QED line
    '''

    def replacer(m):
        header = m.group(1)
        footer = m.group(3)
        indented = _indent(tactics, "  ")
        return f"{header}{indented}{footer}"

    new_content = re.sub(pattern, replacer, content, flags=re.DOTALL | re.VERBOSE)
    if new_content == content:
        raise ValueError(f"Theorem '{name}' not found")
    return new_content


def _indent(text: str, prefix: str) -> str:
    """Indent non-empty lines."""
    return '\n'.join(
        prefix + line if line.strip() else line
        for line in text.split('\n')
    )


def parse_p_output(output: str) -> str | None:
    """Extract tactic script from p() output.

    p() output formats:
    1. Multi-line (proof in progress):
       > p();
       tac1 \\ tac2 >- (...) ...
       val it = () : unit

    2. Single-line (proof complete):
       val it = REWRITE_TAC[]: proof

    Returns None if output contains errors or no valid tactic script.
    """
    # Reject error output before parsing
    stripped = output.lstrip()
    if stripped.startswith('ERROR:') or stripped.startswith('Error:'):
        return None
    if 'Exception' in output or 'HOL_ERR' in output or 'No goalstack' in output or output.startswith('TIMEOUT'):
        return None

    lines = output.split('\n')
    tactic_lines = []

    for line in lines:
        stripped = line.strip()
        # Skip command echo and prompts
        if stripped.startswith('>') or stripped == 'p();':
            continue
        # Handle "val it = TACTIC: proof" format (completed proof)
        if stripped.startswith('val it = ') and ': proof' in stripped:
            tactic = stripped[len('val it = '):]
            tactic = tactic.rsplit(': proof', 1)[0].strip()
            if tactic:
                return tactic
            continue
        # Handle multi-line "val it =" format (completed proof spanning lines)
        if stripped == 'val it =':
            continue
        # Stop at other val bindings
        if stripped.startswith('val '):
            break
        # Handle ": proof" terminator for multi-line val it format
        if stripped == ': proof':
            break
        if stripped.endswith(': proof'):
            tactic_lines.append(stripped.rsplit(': proof', 1)[0].rstrip())
            break
        # Skip "OK" markers from goaltree
        if stripped == 'OK':
            continue
        # Collect tactic content
        if stripped:
            tactic_lines.append(line.rstrip())

    return '\n'.join(tactic_lines).strip() or None
