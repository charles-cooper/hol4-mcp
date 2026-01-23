# hol4-mcp - Repository Specification

MCP server and tools for HOL4 theorem prover interaction.

## Purpose

Provides infrastructure for AI agents to interact with HOL4:
- MCP server exposing HOL4 tools
- HOL subprocess management with null-byte framing
- Proof cursor for file-based workflows
- SML file parsing

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    MCP Server                                │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  hol_start, hol_send, hol_interrupt, holmake         │   │
│  │  hol_cursor_init, hol_cursor_complete, ...           │   │
│  └──────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
          │                           │
          ▼                           ▼
┌──────────────────┐      ┌──────────────────────────────────┐
│   HOL Session    │      │        Proof Cursor              │
│  ┌────────────┐  │      │  ┌────────────┐  ┌────────────┐  │
│  │ subprocess │  │      │  │ file parse │  │  splicing  │  │
│  │ null-byte  │  │      │  │ cheat find │  │  goaltree  │  │
│  └────────────┘  │      │  └────────────┘  └────────────┘  │
└──────────────────┘      └──────────────────────────────────┘
          │
          ▼
┌─────────────────────────────────────────────────────────────┐
│                    HOL4 Process                              │
│                    hol --zero                                │
└─────────────────────────────────────────────────────────────┘
```

## Package Structure

```
hol4_mcp/
  __init__.py           # Package exports
  hol_mcp_server.py     # MCP server (FastMCP)
  hol_session.py        # HOL subprocess wrapper
  hol_cursor.py         # File-based proof cursor
  hol_file_parser.py    # SML parsing
  sml_helpers/
    etq.sml             # Tactic extraction for goaltree mode
    cheat_finder.sml    # Pre-cheat tactic extraction

tests/                  # pytest tests
repo_prompt/            # Recovery prompts
```

## Key Concepts

### Null-Byte Framing

HOL4 started with `--zero` flag delimits messages with `\0`. This enables reliable parsing of multi-line output.

### Goaltree Mode

Uses `gt`/`etq`/`p()` instead of goalstack. `etq` records tactic names as strings, enabling `p()` to extract the proof script.

### Session Registry

In-memory dict mapping session names to `SessionEntry`. Sessions survive across Claude context handoffs (when MCP server is imported, not spawned).

### Cursor Workflow

`init → (prove → complete → splice → reenter) × N → done`

The cursor tracks position in an SML file, managing proof lifecycle from first cheat to completion.

## Component Recovery Prompts

| Component | Recovery Prompt |
|-----------|-----------------|
| MCP Server | [mcp_server.md](mcp_server.md) - Tools, session registry |
| HOL Session | [session.md](session.md) - Subprocess, null-byte, interrupt |
| Proof Cursor | [cursor.md](cursor.md) - File parsing, splicing, goaltree |

## Recreating This Package

**Order of implementation:**

1. **HOL Session** ([session.md](session.md))
   - Null-byte framing with `hol --zero`
   - Process group isolation for interrupt
   - Load etq.sml for tactic extraction

2. **File Parser** (in [cursor.md](cursor.md))
   - Parse Theorem/Triviality/Definition blocks
   - Identify cheats, extract proof bodies
   - Splice completed proofs

3. **Proof Cursor** ([cursor.md](cursor.md))
   - Track position in file
   - Load context, manage goaltree
   - Complete and advance workflow

4. **MCP Server** ([mcp_server.md](mcp_server.md))
   - Session registry
   - Tool functions wrapping session/cursor
   - Holmake integration

## Usage

```python
from hol4_mcp import mcp, HOLSession, ProofCursor

# As MCP server
# Typically imported by orchestrator, not run standalone

# Direct usage
session = HOLSession("/path/to/project")
await session.start()
result = await session.send("1 + 1;")
```
