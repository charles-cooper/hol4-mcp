# Pi Extension

This TypeScript file is a [pi](https://github.com/badlogic/pi-mono) extension that provides HOL4 tools to the LLM agent.

## Installation

```bash
hol4-mcp install-pi
```

This copies `hol4-mcp.ts` to `~/.pi/agent/extensions/`.

## How It Works

The extension spawns hol4-mcp as a subprocess and dynamically discovers all MCP tools, registering them as pi tools available to the agent.
