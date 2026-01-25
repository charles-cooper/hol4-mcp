"""Proof cursor for navigating through theorems without reloading."""

import asyncio
import hashlib
from dataclasses import dataclass, field
from pathlib import Path

from .hol_file_parser import (
    TheoremInfo, parse_file, parse_p_output, parse_theorems,
    TacticSpan, build_line_starts, parse_linearize_with_spans_output,
    make_tactic_spans, offset_to_line_col, line_col_to_offset, HOLParseError,
    _find_json_line, parse_step_positions_output, parse_prefix_commands_output,
)
from .hol_session import HOLSession, HOLDIR, escape_sml_string


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
    - The word "Exception" in identifiers (e.g., "no_ReturnException")
    """
    if output.startswith("TIMEOUT"):
        return True
    if output.lstrip().startswith("ERROR:") or output.lstrip().startswith("Error:"):
        return True
    # Poly/ML uncaught exception format: "Exception- Fail ..." or "Exception- HOL_ERR ..."
    if any(line.startswith("Exception- ") for line in output.split('\n')):
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


# =============================================================================
# FileProofCursor - File-centric proof state inspection
# =============================================================================

@dataclass
class StateAtResult:
    """Result of state_at() call."""
    goals: list[dict]         # Current goals: [{"asms": [...], "goal": "..."}, ...]
    tactic_idx: int           # Index of tactic at position (0-based)
    tactics_replayed: int     # Number of tactics replayed to reach this state
    tactics_total: int        # Total tactics in proof
    file_hash: str            # Content hash when this state was computed
    error: str | None = None  # Error message if replay failed
    timings: dict[str, float] | None = None  # Timing breakdown (ms)


@dataclass
class TheoremCheckpoint:
    """Checkpoint state for a theorem."""
    theorem_name: str
    tactics_count: int            # Number of tactics when checkpoint saved
    end_of_proof_path: Path | None = None   # Checkpoint after all tactics (for state_at)


class FileProofCursor:
    """File-centric proof cursor - agent edits file, cursor inspects state.

    Key design principles:
    - Content hash for change detection (poll-on-demand, no watchdog)
    - Single active theorem at a time
    - Agent edits file directly; cursor is read-only inspector
    - Replay from theorem start for correctness
    """

    def __init__(self, source_file: Path, session: HOLSession, *,
                 checkpoint_dir: Path | None = None, mode: str = "g",
                 tactic_timeout: float = 5.0):
        """Initialize file proof cursor.

        Args:
            source_file: Path to the SML script
            session: HOL session to use
            checkpoint_dir: Where to store checkpoints (default: .hol/cursor_checkpoints/)
            mode: "g" for goalstack (default) or "gt" for goaltree
                  - goalstack: uses g/e(tactic)/b, no proof extraction
                  - goaltree: uses gt/etq "tactic"/backup, p() extracts proof script
            tactic_timeout: Max seconds per tactic (default 5.0, None=unlimited)
        """
        self.file = source_file
        self.session = session

        # Mode: "g" (goalstack) or "gt" (goaltree)
        if mode not in ("g", "gt"):
            raise ValueError(f"mode must be 'g' or 'gt', got '{mode}'")
        self._mode = mode
        
        # Tactic timeout for build discipline
        self._tactic_timeout = tactic_timeout

        # Checkpoint directory: .hol/cursor_checkpoints/ (alongside holmake artifacts)
        if checkpoint_dir is None:
            self._checkpoint_dir = source_file.parent / ".hol" / "cursor_checkpoints"
        else:
            self._checkpoint_dir = checkpoint_dir

        # Cached file state
        self._content: str = ""
        self._content_hash: str = ""
        self._line_starts: list[int] = []
        self._theorems: list[TheoremInfo] = []

        # Active theorem state
        self._active_theorem: str | None = None
        self._active_tactics: list[TacticSpan] = []  # Deprecated, kept for compatibility
        self._step_positions: list[int] = []  # End offsets for each step (relative to proof body)
        self._current_tactic_idx: int = 0  # Current position in proof (for backup optimization)
        self._current_offset: int = -1  # Current proof body offset (-1 = not set)
        self._proof_initialized: bool = False  # Whether g/gt has been called for current theorem

        # What's been loaded into HOL
        self._loaded_to_line: int = 0
        self._loaded_content_hash: str = ""  # Hash of content up to _loaded_to_line

        # Completed theorems this session
        self._completed: set[str] = set()

        # Checkpoint cache: theorem_name -> TheoremCheckpoint
        self._checkpoints: dict[str, TheoremCheckpoint] = {}

    def _compute_hash(self, content: str) -> str:
        """Compute SHA256 hash of content."""
        return hashlib.sha256(content.encode()).hexdigest()

    def _first_changed_line(self, old_content: str, new_content: str) -> int | None:
        """Return first line number (1-indexed) where content differs, or None if identical."""
        old_lines = old_content.split('\n')
        new_lines = new_content.split('\n')

        for i, (old, new) in enumerate(zip(old_lines, new_lines)):
            if old != new:
                return i + 1

        # Length difference (lines added/removed at end)
        if len(old_lines) != len(new_lines):
            return min(len(old_lines), len(new_lines)) + 1

        return None

    def _reparse_if_changed(self) -> bool:
        """Re-read and parse file if content changed. Returns True if changed."""
        content = self.file.read_text()
        content_hash = self._compute_hash(content)

        if content_hash == self._content_hash:
            return False

        # Find first changed line before updating
        old_content = self._content
        first_changed = self._first_changed_line(old_content, content)

        self._content = content
        self._content_hash = content_hash
        self._line_starts = build_line_starts(content)
        self._theorems = parse_theorems(content)

        # Invalidate checkpoints for theorems at or after the change
        if first_changed is not None:
            self._invalidate_checkpoints_from(first_changed)
            # Also reset loaded context tracking - can't trust context after change point
            if first_changed <= self._loaded_to_line:
                self._loaded_to_line = max(0, first_changed - 1)
                self._loaded_content_hash = None

        # Clear active theorem if it was renamed/deleted
        if self._active_theorem:
            if not any(t.name == self._active_theorem for t in self._theorems):
                self._active_theorem = None
                self._active_tactics = []

        return True

    def _get_theorem(self, name: str) -> TheoremInfo | None:
        """Get theorem by name from cached parse."""
        for thm in self._theorems:
            if thm.name == name:
                return thm
        return None

    def _get_theorem_at_position(self, line: int) -> TheoremInfo | None:
        """Get theorem containing the given line number."""
        for thm in self._theorems:
            # Theorem spans from Theorem keyword to QED
            # proof_start_line is line of Proof keyword
            # proof_end_line is line of last proof content (before QED)
            # We consider valid range as: start_line to proof_end_line (inclusive)
            if thm.start_line <= line <= thm.proof_end_line:
                return thm
        return None

    def _check_stale_state(self) -> bool:
        """Check if loaded content has changed (stale HOL state)."""
        if self._loaded_to_line == 0:
            return False
        # Compare hash of content up to loaded line
        loaded_content = '\n'.join(self._content.split('\n')[:self._loaded_to_line - 1])
        return self._compute_hash(loaded_content) != self._loaded_content_hash

    # =========================================================================
    # Checkpoint Management
    # =========================================================================

    def _get_checkpoint_path(self, theorem_name: str, checkpoint_type: str) -> Path:
        """Get path for a checkpoint file."""
        # Sanitize theorem name for filename
        safe_name = theorem_name.replace("/", "_").replace("\\", "_")
        return self._checkpoint_dir / f"{safe_name}_{checkpoint_type}.save"

    def _is_checkpoint_valid(self, theorem_name: str) -> bool:
        """Check if cached checkpoint exists and file is present."""
        ckpt = self._checkpoints.get(theorem_name)
        if not ckpt:
            return False
        if not ckpt.end_of_proof_path or not ckpt.end_of_proof_path.exists():
            return False
        return True

    async def _save_end_of_proof_checkpoint(self, theorem_name: str, tactics_count: int) -> bool:
        """Save checkpoint after all tactics have been replayed.

        Call this when goaltree has all tactics applied. The checkpoint
        captures this state for fast state_at via loadState + backup_n.

        Returns True if checkpoint was saved successfully.
        """
        self._checkpoint_dir.mkdir(parents=True, exist_ok=True)
        ckpt_path = self._get_checkpoint_path(theorem_name, "end_of_proof")

        # Save child checkpoint (incremental, ~35-45ms, 1-7MB)
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path}", 1);', timeout=30
        )
        if _is_hol_error(result):
            return False

        self._checkpoints[theorem_name] = TheoremCheckpoint(
            theorem_name=theorem_name,
            tactics_count=tactics_count,
            end_of_proof_path=ckpt_path,
        )
        return True

    async def _load_checkpoint_and_backup(self, theorem_name: str, target_tactic_idx: int) -> bool:
        """Load checkpoint and backup to target position.

        Args:
            theorem_name: Theorem whose checkpoint to load
            target_tactic_idx: Target tactic index (0 = initial state, N = after N tactics)

        Returns True if successful, False if checkpoint invalid or load failed.
        """
        ckpt = self._checkpoints.get(theorem_name)
        if not ckpt or not self._is_checkpoint_valid(theorem_name):
            return False

        # Load checkpoint (~70-120ms depending on loaded theories)
        result = await self.session.send(
            f'PolyML.SaveState.loadState "{ckpt.end_of_proof_path}";', timeout=30
        )
        if _is_hol_error(result):
            return False

        # Backup to target position (~11ms for any N)
        backups_needed = ckpt.tactics_count - target_tactic_idx
        if backups_needed > 0:
            result = await self.session.send(f'backup_n {backups_needed};', timeout=30)
            if _is_hol_error(result):
                return False

        self._current_tactic_idx = target_tactic_idx
        self._proof_initialized = True
        return True

    def _invalidate_checkpoint(self, theorem_name: str) -> None:
        """Invalidate and delete checkpoint for a theorem."""
        ckpt = self._checkpoints.pop(theorem_name, None)
        if ckpt and ckpt.end_of_proof_path and ckpt.end_of_proof_path.exists():
            ckpt.end_of_proof_path.unlink()

    def _invalidate_all_checkpoints(self) -> None:
        """Invalidate all checkpoints (e.g., when file changes significantly)."""
        for name in list(self._checkpoints.keys()):
            self._invalidate_checkpoint(name)

    def _invalidate_checkpoints_from(self, start_line: int) -> None:
        """Invalidate checkpoints for theorems at or after start_line.

        When content changes at line N, all theorems starting at N or later
        have invalid checkpoints (their context may have changed).
        """
        for thm in self._theorems:
            if thm.start_line >= start_line:
                self._invalidate_checkpoint(thm.name)

    async def init(self) -> dict:
        """Initialize cursor - parse file, load deps, verify theorems.

        Returns:
            dict with:
              - theorems: list of {name, line, has_cheat}
              - cheats: list of cheat locations
              - verified: number of verified non-cheat theorems
              - total_non_cheat: total non-cheat theorems
              - broken: {name, line, error} if a theorem is broken, else None
              - error: error message if init failed
        """
        self._reparse_if_changed()

        if not self._theorems:
            return {"error": "No theorems found in file", "theorems": [], "cheats": []}

        if not self.session.is_running:
            await self.session.start()

        # Load dependencies
        try:
            deps = await get_script_dependencies(self.file)
            for dep in deps:
                await self.session.send(f'load "{dep}";', timeout=60)
        except FileNotFoundError:
            pass  # holdeptool not available, skip dep loading

        thm_list = [
            {"name": t.name, "line": t.start_line, "has_cheat": t.has_cheat}
            for t in self._theorems
        ]
        # Return cheat info with line/col for direct use with state_at
        cheats = [
            {
                "theorem": t.name,
                "line": t.proof_start_line,  # Line of first proof content
                "col": 1,
            }
            for t in self._theorems if t.has_cheat
        ]

        # Verify all non-cheat theorems (stop on first failure)
        verify_result = await self._verify_all_theorems()
        
        return {
            "theorems": thm_list,
            "cheats": cheats,
            "verified": verify_result.get("verified", 0),
            "total_non_cheat": verify_result.get("total", 0),
            "broken": verify_result.get("broken"),  # None if all pass
        }

    async def _verify_all_theorems(self) -> dict:
        """Verify all non-cheat theorems by replaying their tactics.
        
        Stops on first failure. Builds checkpoints for verified theorems.
        
        Returns:
            dict with:
              - verified: number of successfully verified theorems
              - total: total non-cheat theorems
              - broken: {name, line, error} if a theorem is broken, else None
        """
        non_cheat_thms = [t for t in self._theorems if not t.has_cheat]
        verified = 0
        
        for thm in non_cheat_thms:
            # Use state_at to replay all tactics (goes to end of proof)
            # This will enter the theorem, load context, and replay tactics
            end_line = thm.proof_end_line - 1  # Line before QED
            result = await self.state_at(end_line)
            
            # Check for tactic errors (not goals_json errors)
            # If all tactics replayed but goals_json says "no goals", that's actually success
            is_no_goals_error = (
                result.error and 
                "no goals" in result.error.lower() and
                result.tactics_replayed == result.tactics_total
            )
            
            if result.error and not is_no_goals_error:
                return {
                    "verified": verified,
                    "total": len(non_cheat_thms),
                    "broken": {
                        "name": thm.name,
                        "line": thm.start_line,
                        "error": result.error,
                    }
                }
            
            # Check that proof is complete (no remaining goals)
            # Empty goals with no error OR "no goals" error = proof complete
            if result.goals and not is_no_goals_error:
                return {
                    "verified": verified,
                    "total": len(non_cheat_thms),
                    "broken": {
                        "name": thm.name,
                        "line": thm.start_line,
                        "error": f"Proof incomplete: {len(result.goals)} goals remaining",
                    }
                }
            
            verified += 1
        
        return {"verified": verified, "total": len(non_cheat_thms), "broken": None}

    async def enter_theorem(self, name: str) -> dict:
        """Enter a theorem for proof state inspection.

        Loads context up to theorem start, parses tactics, sets up for state_at.

        Args:
            name: Theorem name to enter

        Returns:
            dict with:
              - theorem: theorem name
              - goal: theorem goal
              - tactics: number of tactics in proof
              - has_cheat: whether proof has cheat
              - error: error message if failed
        """
        self._reparse_if_changed()

        thm = self._get_theorem(name)
        if not thm:
            return {"error": f"Theorem '{name}' not found"}

        # Load context up to theorem start (if not already loaded)
        if thm.start_line > self._loaded_to_line:
            content_lines = self._content.split('\n')
            # _loaded_to_line=0 means nothing loaded, so start from line 0 (index 0)
            # _loaded_to_line=N means lines 1..N-1 loaded, so start from index N-1
            start_idx = max(0, self._loaded_to_line - 1) if self._loaded_to_line > 0 else 0
            to_load = '\n'.join(content_lines[start_idx:thm.start_line - 1])
            if to_load.strip():
                result = await self.session.send(to_load, timeout=300)
                if _is_hol_error(result):
                    return {"error": f"Failed to load context: {result[:300]}"}

            # Update loaded tracking
            loaded_content = '\n'.join(content_lines[:thm.start_line - 1])
            self._loaded_to_line = thm.start_line
            self._loaded_content_hash = self._compute_hash(loaded_content)

        # Parse step positions from proof body using TacticParse
        if thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)
            step_result = await self.session.send(
                f'step_positions_json "{escaped_body}";', timeout=30
            )
            try:
                self._step_positions = parse_step_positions_output(step_result)
            except HOLParseError as e:
                return {"error": f"Failed to parse step positions: {e}"}
        else:
            self._step_positions = []

        self._active_theorem = name
        self._active_tactics = []  # Deprecated
        self._current_tactic_idx = 0  # Reset position for new theorem
        self._proof_initialized = False  # Will be set on first state_at

        return {
            "theorem": name,
            "goal": thm.goal,
            "tactics": len(self._step_positions),
            "has_cheat": thm.has_cheat,
        }

    async def state_at(self, line: int, col: int = 1) -> StateAtResult:
        """Get proof state at file position using prefix-based replay.

        Uses HOL's TacticParse.sliceTacticBlock to generate a valid prefix
        for any position, then executes it with a single e() call.

        Auto-enters the theorem containing the position if not already active.

        Args:
            line: 1-indexed line number
            col: 1-indexed column number (default 1)

        Returns:
            StateAtResult with goals, tactic index, etc.
        """
        import time
        timings: dict[str, float] = {}
        t0 = time.perf_counter()

        # Reparse if file changed
        changed = self._reparse_if_changed()
        timings['reparse'] = time.perf_counter() - t0

        # Find theorem at position and auto-enter if needed
        thm_at_pos = self._get_theorem_at_position(line)
        if not thm_at_pos:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash,
                error=f"Position ({line}, {col}) is not within any theorem"
            )

        # Auto-enter theorem if different from active
        t1 = time.perf_counter()
        if self._active_theorem != thm_at_pos.name:
            enter_result = await self.enter_theorem(thm_at_pos.name)
            if "error" in enter_result:
                return StateAtResult(
                    goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                    file_hash=self._content_hash, error=enter_result["error"]
                )
            changed = True  # Force re-check since we just entered
        timings['enter_theorem'] = time.perf_counter() - t1

        thm = self._get_theorem(self._active_theorem)
        if not thm:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash, error=f"Theorem '{self._active_theorem}' no longer exists"
            )

        # If file changed, invalidate checkpoint and re-parse step positions
        t2 = time.perf_counter()
        if changed:
            self._invalidate_checkpoint(self._active_theorem)
            if thm.proof_body:
                escaped_body = escape_sml_string(thm.proof_body)
                step_result = await self.session.send(
                    f'step_positions_json "{escaped_body}";', timeout=30
                )
                try:
                    self._step_positions = parse_step_positions_output(step_result)
                except HOLParseError as e:
                    return StateAtResult(
                        goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                        file_hash=self._content_hash,
                        error=f"Failed to parse step positions: {e}"
                    )
            else:
                self._step_positions = []
        timings['parse_steps'] = time.perf_counter() - t2

        # Check if position is within theorem bounds (include QED line)
        # proof_end_line is "line after QED", so QED is at proof_end_line - 1
        proof_keyword_line = thm.proof_start_line - 1
        qed_line = thm.proof_end_line - 1
        if line < proof_keyword_line or line > qed_line:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash,
                error=f"Position ({line}, {col}) not in theorem '{self._active_theorem}' "
                      f"(valid lines {proof_keyword_line}-{qed_line})"
            )

        # Convert (line, col) to proof body offset
        # If on QED line, use end of proof body
        if line == qed_line:
            proof_body_offset = len(thm.proof_body)
        else:
            file_offset = line_col_to_offset(line, col, self._line_starts)
            proof_body_offset = max(0, file_offset - thm.proof_body_offset)

        # Find tactic index for reporting (which step boundary we're at/past)
        tactic_idx = 0
        for i, end_pos in enumerate(self._step_positions):
            if proof_body_offset >= end_pos:
                tactic_idx = i + 1
            else:
                break

        total_tactics = len(self._step_positions)
        error_msg = None
        t3 = time.perf_counter()

        # Calculate step boundary info for O(1) access
        # step_before_end: end offset of last complete step (0 if none)
        step_before_end = self._step_positions[tactic_idx - 1] if tactic_idx > 0 else 0
        # Only execute partial at proof end. Within a step, partial_step_commands may return
        # the full step (for atomic tactics), which we don't want to execute.
        # Fine-grained stepping within compound tactics is sacrificed for correctness.
        need_partial = tactic_idx >= total_tactics and proof_body_offset > step_before_end
        actual_replayed = 0
        escaped_body = escape_sml_string(thm.proof_body) if thm.proof_body else ""

        # Try O(1) path: checkpoint + backup_n
        used_checkpoint = False
        if self._is_checkpoint_valid(self._active_theorem) and thm.proof_body:
            # Load checkpoint (at proof end) and backup to target step
            if await self._load_checkpoint_and_backup(self._active_theorem, tactic_idx):
                used_checkpoint = True
                actual_replayed = tactic_idx

        if not used_checkpoint:
            # Build checkpoint: replay all steps, then backup
            await self.session.send('drop_all();', timeout=5)
            goal = thm.goal.replace('\n', ' ').strip()
            goal_cmd = "g" if self._mode == "g" else "gt"
            gt_result = await self.session.send(f'{goal_cmd} `{goal}`;', timeout=30)
            if _is_hol_error(gt_result):
                self._proof_initialized = False
                return StateAtResult(
                    goals=[], tactic_idx=tactic_idx, tactics_replayed=0,
                    tactics_total=total_tactics, file_hash=self._content_hash,
                    error=f"Failed to set up goal: {gt_result[:300]}"
                )
            self._proof_initialized = True

            if thm.proof_body and total_tactics > 0:
                # Execute all steps individually for backup_n to work
                step_result = await self.session.send(
                    f'step_commands_json "{escaped_body}";', timeout=30
                )
                try:
                    step_cmds = parse_prefix_commands_output(step_result)
                except HOLParseError as e:
                    error_msg = f"Failed to get step commands: {e}"
                    step_cmds = ""

                if step_cmds.strip():
                    batch_timeout = max(30, int(self._tactic_timeout * total_tactics)) if self._tactic_timeout else 300
                    result = await self.session.send(step_cmds, timeout=batch_timeout)
                    if _is_hol_error(result):
                        if result.startswith("TIMEOUT"):
                            error_msg = f"Tactic replay timed out (>{batch_timeout}s)"
                        else:
                            error_msg = f"Tactic replay failed: {result[:200]}"
                    else:
                        # Save checkpoint at proof end
                        await self._save_end_of_proof_checkpoint(self._active_theorem, total_tactics)
                        # Backup to target position
                        backups_needed = total_tactics - tactic_idx
                        if backups_needed > 0:
                            await self.session.send(f'backup_n {backups_needed};', timeout=30)
                        actual_replayed = tactic_idx

        # If fine-grained position (within a step), execute partial
        if need_partial and not error_msg and thm.proof_body:
            partial_result = await self.session.send(
                f'partial_step_commands_json "{escaped_body}" {step_before_end} {proof_body_offset};',
                timeout=30
            )
            try:
                partial_cmd = parse_prefix_commands_output(partial_result)
            except HOLParseError as e:
                error_msg = f"Failed to get partial step commands: {e}"
                partial_cmd = ""

            if partial_cmd.strip():
                result = await self.session.send(partial_cmd, timeout=self._tactic_timeout or 30)
                if _is_hol_error(result):
                    error_msg = f"Partial step failed: {result[:200]}"

        timings['replay'] = time.perf_counter() - t3
        timings['used_checkpoint'] = 1.0 if used_checkpoint else 0.0

        # Get current goals as JSON
        t4 = time.perf_counter()
        goals_output = await self.session.send('goals_json();', timeout=10)
        try:
            goals = self._parse_goals_json(goals_output)
        except HOLParseError as e:
            goals = []
            error_msg = str(e) if not error_msg else f"{error_msg}; {e}"
        timings['goals'] = time.perf_counter() - t4

        timings['total'] = time.perf_counter() - t0

        return StateAtResult(
            goals=goals,
            tactic_idx=tactic_idx,
            tactics_replayed=actual_replayed,
            tactics_total=total_tactics,
            file_hash=self._content_hash,
            error=error_msg,
            timings=timings,
        )

    def _parse_goals_json(self, output: str) -> list[dict]:
        """Parse JSON goal output from goals_json().

        Output format: {"ok":[{"asms":[...], "goal":"..."}, ...]} or {"err":"message"}
        Returns: List of goal dicts with 'asms' (list of assumption strings) and 'goal' (conclusion string)
        Raises: HOLParseError if HOL4 returned an error or output is malformed.
        """
        result = _find_json_line(output, "goals_json")

        if 'ok' in result:
            goals = []
            for g in result['ok']:
                if isinstance(g, dict) and 'asms' in g and 'goal' in g:
                    goals.append(g)
                else:
                    # Old format (just goal string) for backwards compat
                    goals.append({"asms": [], "goal": str(g)})
            return goals
        elif 'err' in result:
            raise HOLParseError(f"goals_json: {result['err']}")
        else:
            raise HOLParseError(f"Unexpected JSON structure: {result}")

    @property
    def status(self) -> dict:
        """Get cursor status."""
        self._reparse_if_changed()
        stale = self._check_stale_state()

        return {
            "file": str(self.file),
            "file_hash": self._content_hash,
            "active_theorem": self._active_theorem,
            "active_tactics": len(self._step_positions),
            "loaded_to_line": self._loaded_to_line,
            "stale": stale,
            "completed": list(self._completed),
            "theorems": [
                {"name": t.name, "line": t.start_line, "has_cheat": t.has_cheat}
                for t in self._theorems
            ],
            "cheats": [
                {"theorem": t.name, "line": t.proof_start_line, "col": 1}
                for t in self._theorems if t.has_cheat and t.name not in self._completed
            ],
        }
