"""Proof cursor for navigating through theorems without reloading."""

import asyncio
from pathlib import Path

from .hol_file_parser import TheoremInfo, parse_file, parse_p_output
from .hol_session import HOLSession, HOLDIR, escape_sml_string


def _parse_sml_string(output: str) -> str:
    """Extract string value from SML output like 'val it = "...": string'.

    Returns the raw escaped content - DO NOT unescape, as we pass this
    directly to another SML string literal (etq).
    """
    for line in output.split('\n'):
        line = line.strip()
        if line.startswith('val it = "'):
            # Handle both 'val it = "...": string' and 'val it = "..." : string'
            for suffix in ['": string', '" : string']:
                if suffix in line:
                    start = line.index('"') + 1
                    end = line.rindex(suffix)
                    return line[start:end]  # Keep SML escaping intact
    return ""


def _parse_sml_string_list(output: str) -> list[str]:
    """Extract string list from SML output like 'val it = ["a", "b"]: string list'.

    Returns list of raw escaped strings for passing to etq.
    """
    for line in output.split('\n'):
        if 'val it = [' in line:
            start = line.index('[')
            end = line.rindex(']') + 1
            list_str = line[start:end]
            if list_str == '[]':
                return []
            # Parse SML string list: ["a", "b", ...]
            items = []
            in_string = False
            escaped = False
            current = ""
            for c in list_str[1:-1]:  # skip [ and ]
                if escaped:
                    current += c
                    escaped = False
                elif c == '\\':
                    current += c
                    escaped = True
                elif c == '"':
                    if in_string:
                        items.append(current)
                        current = ""
                    in_string = not in_string
                elif in_string:
                    current += c
            return items
    return []


def _parse_linearize_result(output: str) -> tuple[list[str], int | None]:
    """Extract (tactics, cheat_offset) from linearize_to_cheat output.

    Format: val it = (["tac1", "tac2"], SOME 42): string list * int option
    Or:     val it = ([], NONE): string list * int option
    """
    for line in output.split('\n'):
        if 'val it = (' not in line:
            continue
        try:
            list_start = line.index('[')

            # Find matching ] by tracking bracket depth and string state
            depth = 0
            in_string = False
            escaped = False
            list_end = list_start
            for i, c in enumerate(line[list_start:], list_start):
                if escaped:
                    escaped = False
                elif c == '\\' and in_string:
                    escaped = True
                elif c == '"':
                    in_string = not in_string
                elif not in_string:
                    if c == '[':
                        depth += 1
                    elif c == ']':
                        depth -= 1
                        if depth == 0:
                            list_end = i + 1
                            break

            list_str = line[list_start:list_end]

            # Parse string list
            tactics = []
            if list_str != '[]':
                in_string = False
                escaped = False
                current = ""
                for c in list_str[1:-1]:
                    if escaped:
                        current += c
                        escaped = False
                    elif c == '\\':
                        current += c
                        escaped = True
                    elif c == '"':
                        if in_string:
                            tactics.append(current)
                            current = ""
                        in_string = not in_string
                    elif in_string:
                        current += c

            # Parse offset: look for SOME N or NONE after the list
            rest = line[list_end:]
            offset = None
            if 'SOME' in rest:
                import re
                m = re.search(r'SOME\s+(\d+)', rest)
                if m:
                    offset = int(m.group(1))

            return tactics, offset
        except (ValueError, IndexError):
            continue
    return [], None


def _is_hol_error(output: str) -> bool:
    """Check if HOL output indicates an actual error (not just a warning).

    Returns True for real errors like:
    - SML exceptions ("Exception-", "raised exception")
    - HOL errors ("HOL_ERR")
    - Poly/ML errors ("poly: : error:")
    - Tactic failures ("Fail ")
    - TIMEOUT strings from HOL session

    Returns False for:
    - HOL warnings/messages ("<<HOL message:", "<<HOL warning:")
    - The word "error" appearing in goal terms (e.g., "error_state")
    """
    if output.startswith("TIMEOUT"):
        return True
    if output.lstrip().startswith("ERROR:") or output.lstrip().startswith("Error:"):
        return True
    if "Exception" in output:
        return True
    if "HOL_ERR" in output:
        return True
    if "poly: : error:" in output.lower():
        return True
    if "raised exception" in output.lower():
        return True
    # Tactic Fail with message
    if "\nFail " in output or output.startswith("Fail "):
        return True
    return False


async def get_script_dependencies(script_path: Path) -> list[str]:
    """Get dependencies using holdeptool.exe.

    Raises FileNotFoundError if holdeptool.exe doesn't exist.
    """
    holdeptool = HOLDIR / "bin" / "holdeptool.exe"
    if not holdeptool.exists():
        raise FileNotFoundError(f"holdeptool.exe not found at {holdeptool}")

    proc = await asyncio.create_subprocess_exec(
        str(holdeptool), str(script_path),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )
    stdout, stderr = await proc.communicate()
    if proc.returncode != 0:
        raise RuntimeError(f"holdeptool.exe failed: {stderr.decode()}")

    return [line.strip() for line in stdout.decode().splitlines() if line.strip()]


def get_executable_content(content: str, up_to_line: int) -> str:
    """Extract SML content from script up to specified line.

    Returns content from line 1 to up_to_line-1, including any
    Theory/Ancestors/Libs header (which sets up the environment).
    """
    lines = content.split('\n')
    prefix_lines = lines[:up_to_line - 1]
    return '\n'.join(prefix_lines)


class ProofCursor:
    """Track position in file, advance through theorems without reloading."""

    def __init__(self, source_file: Path, session: HOLSession):
        self.file = source_file
        self.session = session
        self.theorems: list[TheoremInfo] = []
        self.position: int = 0
        self._loaded_to_line: int = 0  # Track how much content is loaded

    @property
    def completed(self) -> set[str]:
        """Theorems without cheats (derived from current file state)."""
        return {t.name for t in self.theorems if not t.has_cheat}

    def current(self) -> TheoremInfo | None:
        """Get current theorem."""
        if 0 <= self.position < len(self.theorems):
            return self.theorems[self.position]
        return None

    def next(self) -> TheoremInfo | None:
        """Advance to next theorem."""
        if self.position + 1 < len(self.theorems):
            self.position += 1
            return self.current()
        return None

    def next_cheat(self) -> TheoremInfo | None:
        """Find first theorem with cheat."""
        for i, thm in enumerate(self.theorems):
            if thm.has_cheat:
                self.position = i
                return thm
        return None

    def goto(self, theorem_name: str) -> TheoremInfo | None:
        """Go to specific theorem by name."""
        for i, thm in enumerate(self.theorems):
            if thm.name == theorem_name:
                self.position = i
                return thm
        return None

    async def initialize(self) -> str:
        """Parse file, load HOL to first cheat, position cursor."""
        self.theorems = parse_file(self.file)

        if not self.theorems:
            return "No theorems found in file"

        if not self.session.is_running:
            await self.session.start()

        # Find first cheat
        first_cheat_idx = next(
            (i for i, t in enumerate(self.theorems) if t.has_cheat),
            None
        )

        if first_cheat_idx is None:
            return "No cheats found - all theorems already proved"

        thm = self.theorems[first_cheat_idx]

        # Get and load dependencies
        deps = await get_script_dependencies(self.file)
        for dep in deps:
            await self.session.send(f'load "{dep}";', timeout=60)

        # Load script content up to first cheat
        content = self.file.read_text()
        prefix = get_executable_content(content, thm.start_line)

        if prefix.strip():
            await self.session.send(prefix, timeout=300)

        self._loaded_to_line = thm.start_line
        self.position = first_cheat_idx

        # Compute cheat_line for all theorems with cheats
        await self._compute_cheat_lines()

        return f"Positioned at {thm.name} (line {thm.cheat_line or thm.start_line})"

    async def _compute_cheat_lines(self) -> None:
        """Compute cheat_line for all theorems using SML parser."""
        for thm in self.theorems:
            if thm.has_cheat and thm.proof_body:
                escaped = escape_sml_string(thm.proof_body)
                result = await self.session.send(
                    f'linearize_to_cheat "{escaped}";', timeout=30
                )
                _, offset = _parse_linearize_result(result)
                if offset is not None:
                    thm.cheat_line = thm.proof_start_line + thm.proof_body[:offset].count('\n')

    async def load_context_to(self, target_line: int) -> None:
        """Load file content from current loaded position to target line."""
        if target_line <= self._loaded_to_line:
            return  # Already loaded

        content = self.file.read_text()
        lines = content.split('\n')

        # Get content between loaded position and target
        # _loaded_to_line is 1-indexed line number of first unloaded line
        # Convert to 0-indexed: line N is at index N-1
        additional = '\n'.join(lines[self._loaded_to_line - 1:target_line - 1])

        if additional.strip():
            await self.session.send(additional, timeout=300)

        self._loaded_to_line = target_line

    async def start_current(self) -> str:
        """Set up goaltree for current theorem, replay tactics to cheat point."""
        thm = self.current()
        if not thm:
            return "ERROR: No current theorem"

        # Load any context between previous position and this theorem
        # (e.g., definitions between theorem A and B)
        await self.load_context_to(thm.start_line)

        # Clear all proof state unconditionally
        await self.session.send('drop_all();', timeout=5)

        # Set up goal
        goal = thm.goal.replace('\n', ' ').strip()
        result = await self.session.send(f'gt `{goal}`;', timeout=30)

        if _is_hol_error(result):
            return f"ERROR setting up goal: {result[:500]}"

        # Get pre-cheat tactics using TacticParse
        if thm.has_cheat and thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)

            # linearize_to_cheat returns (tactics, cheat_offset)
            lin_result = await self.session.send(
                f'linearize_to_cheat "{escaped_body}";', timeout=30
            )
            tactics, cheat_offset = _parse_linearize_result(lin_result)

            # Calculate cheat line from SML-provided offset (authoritative)
            if cheat_offset is not None:
                cheat_line = thm.proof_start_line + thm.proof_body[:cheat_offset].count('\n')
                thm.cheat_line = cheat_line  # Store for status displays
            else:
                cheat_line = thm.cheat_line or thm.proof_start_line

            if tactics:
                # Replay each tactic in sequence
                for i, tac in enumerate(tactics):
                    tac_escaped = escape_sml_string(tac)
                    tac_result = await self.session.send(f'etq "{tac_escaped}";', timeout=300)
                    if _is_hol_error(tac_result):
                        return f"ERROR replaying tactic {i+1}/{len(tactics)} '{tac}': {tac_result[:300]}"
                return (f"Ready: {thm.name} (at cheat line {cheat_line}, "
                        f"{len(tactics)} tactics auto-applied from file)")

            # No tactics before cheat (cheat is first thing)
            if cheat_offset is not None:
                return f"Ready: {thm.name} (at cheat line {cheat_line})"

            # Fall back to extract_before_cheat as safety net.
            # In practice, linearize_to_cheat handles all cases extract_before_cheat
            # can handle (plus nested ones). We keep this fallback but can't construct
            # a test case where it triggers - both use the same TacticParse AST.
            extract_result = await self.session.send(
                f'extract_before_cheat "{escaped_body}";', timeout=30
            )
            before_cheat = _parse_sml_string(extract_result)
            if before_cheat:
                tac_result = await self.session.send(f'etq "{before_cheat}";', timeout=300)
                if _is_hol_error(tac_result):
                    return f"ERROR replaying tactics: {tac_result[:300]}"
                line = thm.cheat_line or thm.proof_start_line
                return (f"Ready: {thm.name} (at cheat line {line}, "
                        f"tactics auto-applied from file)")

        if thm.has_cheat:
            line = thm.cheat_line or thm.proof_start_line
            return f"Ready: {thm.name} (at cheat line {line})"
        return f"Ready: {thm.name}"

    async def extract_proof(self) -> dict:
        """Extract proof via p() and drop goal.

        Does NOT modify the filesystem - agent is responsible for splicing.

        Returns dict with:
          - proof: the tactic script from p()
          - theorem: name of theorem
          - error: error message if failed (other fields absent)
        """
        thm = self.current()
        if not thm:
            return {"error": "No current theorem"}

        # Get proof from p()
        p_output = await self.session.send("p();", timeout=30)
        tactic_script = parse_p_output(p_output)

        if not tactic_script:
            return {"error": f"No proof found. Output:\n{p_output}"}

        # Reject proofs with <anonymous> tactics (agent used e() instead of etq)
        if "<anonymous>" in tactic_script:
            return {
                "error": "Proof contains <anonymous> tactics. "
                "Use etq instead of e() to record tactic names."
            }

        # Drop goal
        await self.session.send("drop();", timeout=5)

        # NOTE: We do NOT advance _loaded_to_line here. The theorem was proved
        # interactively, but the agent will splice the proof into the file.
        # When hol_cursor_reenter calls load_context_to for the next theorem,
        # it will load this theorem's block from the (edited) file, storing
        # the theorem in HOL's context for subsequent proofs to reference.

        return {"proof": tactic_script, "theorem": thm.name}

    @property
    def status(self) -> dict:
        """Get cursor status.

        Note: 'cheats' reflects actual file state (theorems with has_cheat=True),
        not filtered by self.completed. This ensures ground truth after reparses.
        """
        current = self.current()
        # Use file state only - self.completed is for navigation, not display
        # cheat_line is set by SML parser; falls back to proof_start_line before that
        cheated_theorems = [
            {"name": t.name, "line": t.cheat_line or t.proof_start_line}
            for t in self.theorems
            if t.has_cheat
        ]
        return {
            "file": str(self.file),
            "current": current.name if current else None,
            "current_line": current.start_line if current else None,
            "position": f"{self.position + 1}/{len(self.theorems)}",
            "completed": list(self.completed),
            "cheated_theorems": cheated_theorems,
        }
