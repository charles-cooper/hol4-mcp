# HOL4 MCP Extension for Pi

Pi extension that provides HOL4 theorem prover tools to the agent via the hol4-mcp server.

## Installation

```bash
# Install the MCP server
pipx install hol4-mcp
# or: uv tool install hol4-mcp

# Copy extension to pi
cp pi-extension/hol4-mcp.ts ~/.pi/agent/extensions/
```

Or run directly:
```bash
pi -e ./pi-extension/hol4-mcp.ts
```

## How It Works

The extension:
1. Spawns the hol4-mcp server as a subprocess via stdio
2. Dynamically discovers all tools from the server via MCP protocol
3. Registers them as pi tools available to the LLM agent
4. Cleans up the server process on session shutdown

## Tools

Tools are dynamically discovered from the MCP server:

### Session Management
- `hol_start` - Start or reconnect HOL session
- `hol_send` - Send SML commands to HOL
- `hol_sessions` - List active sessions
- `hol_interrupt` - Abort runaway tactics
- `hol_stop` - Terminate session
- `hol_restart` - Restart session

### Build
- `holmake` - Build HOL theories
- `hol_log` - View build log for a theory
- `hol_logs` - List available build logs

### Cursor-based Workflow
- `hol_cursor_init` - Initialize cursor-based proof workflow
- `hol_cursor_goto` - Jump to specific theorem
- `hol_cursor_complete` - Complete proof and advance
- `hol_cursor_status` - Show progress
- `hol_cursor_reenter` - Re-enter goaltree for current theorem

## Requirements

- HOL4 installation (HOLDIR environment variable set)
