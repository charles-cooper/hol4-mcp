/**
 * HOL4 MCP Extension for Pi
 *
 * Provides HOL4 theorem prover tools to the agent by connecting to the hol4-mcp server.
 * The server is spawned automatically on first tool use and cleaned up on exit.
 *
 * Tools are dynamically discovered from the MCP server, so changes to the server
 * are automatically reflected without updating this extension.
 */

import { spawn, type ChildProcess } from "node:child_process";
import type { ExtensionAPI } from "@mariozechner/pi-coding-agent";
import { Type, type TSchema } from "@sinclair/typebox";

// Minimal MCP client - JSON-RPC 2.0 over stdio with content-length framing
class McpClient {
  private proc: ChildProcess | null = null;
  private buffer = "";
  private nextId = 1;
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();

  async connect(command: string, args: string[]): Promise<void> {
    this.proc = spawn(command, args, { stdio: ["pipe", "pipe", "pipe"] });

    this.proc.stdout!.on("data", (chunk) => {
      this.buffer += chunk.toString();
      this.processBuffer();
    });

    this.proc.on("error", (err) => {
      for (const { reject } of this.pending.values()) {
        reject(err);
      }
      this.pending.clear();
    });

    this.proc.on("close", () => {
      const err = new Error("MCP server closed");
      for (const { reject } of this.pending.values()) {
        reject(err);
      }
      this.pending.clear();
      this.proc = null;
    });

    // Initialize
    await this.request("initialize", {
      protocolVersion: "2024-11-05",
      capabilities: {},
      clientInfo: { name: "pi-hol4-mcp", version: "0.1.0" },
    });

    // Send initialized notification
    this.notify("notifications/initialized", {});
  }

  private processBuffer(): void {
    while (true) {
      const headerEnd = this.buffer.indexOf("\r\n\r\n");
      if (headerEnd === -1) return;

      const header = this.buffer.slice(0, headerEnd);
      const match = header.match(/Content-Length:\s*(\d+)/i);
      if (!match) {
        this.buffer = this.buffer.slice(headerEnd + 4);
        continue;
      }

      const contentLength = parseInt(match[1], 10);
      const contentStart = headerEnd + 4;
      if (this.buffer.length < contentStart + contentLength) return;

      const content = this.buffer.slice(contentStart, contentStart + contentLength);
      this.buffer = this.buffer.slice(contentStart + contentLength);

      try {
        const msg = JSON.parse(content);
        if ("id" in msg && this.pending.has(msg.id)) {
          const { resolve, reject } = this.pending.get(msg.id)!;
          this.pending.delete(msg.id);
          if (msg.error) {
            reject(new Error(msg.error.message || JSON.stringify(msg.error)));
          } else {
            resolve(msg.result);
          }
        }
      } catch {
        // Ignore parse errors
      }
    }
  }

  private send(msg: object): void {
    if (!this.proc?.stdin) throw new Error("Not connected");
    const json = JSON.stringify(msg);
    const frame = `Content-Length: ${Buffer.byteLength(json)}\r\n\r\n${json}`;
    this.proc.stdin.write(frame);
  }

  private notify(method: string, params: object): void {
    this.send({ jsonrpc: "2.0", method, params });
  }

  request<T = any>(method: string, params: object): Promise<T> {
    return new Promise((resolve, reject) => {
      const id = this.nextId++;
      this.pending.set(id, { resolve, reject });
      this.send({ jsonrpc: "2.0", id, method, params });
    });
  }

  async listTools(): Promise<{ tools: Array<{ name: string; description?: string; inputSchema?: any }> }> {
    return this.request("tools/list", {});
  }

  async callTool(name: string, args: Record<string, unknown>): Promise<{ content: Array<{ type: string; text?: string }>; isError?: boolean }> {
    return this.request("tools/call", { name, arguments: args });
  }

  close(): void {
    if (this.proc) {
      this.proc.kill();
      this.proc = null;
    }
  }
}

// Convert MCP JSON Schema to TypeBox schema
function jsonSchemaToTypebox(schema: any): TSchema {
  if (!schema || typeof schema !== "object") {
    return Type.Any();
  }

  switch (schema.type) {
    case "string":
      return Type.String({ description: schema.description });
    case "number":
    case "integer":
      return Type.Number({ description: schema.description });
    case "boolean":
      return Type.Boolean({ description: schema.description });
    case "array":
      return Type.Array(jsonSchemaToTypebox(schema.items || {}), { description: schema.description });
    case "object": {
      const properties: Record<string, TSchema> = {};
      const required = new Set(schema.required || []);

      for (const [key, value] of Object.entries(schema.properties || {})) {
        const propSchema = jsonSchemaToTypebox(value);
        properties[key] = required.has(key) ? propSchema : Type.Optional(propSchema);
      }
      return Type.Object(properties, { description: schema.description });
    }
    default:
      return Type.Any({ description: schema.description });
  }
}

export default function hol4McpExtension(pi: ExtensionAPI) {
  let client: McpClient | null = null;
  let connecting: Promise<McpClient> | null = null;
  let toolsRegistered = false;

  async function getClient(): Promise<McpClient> {
    if (client) return client;
    if (connecting) return connecting;

    connecting = (async () => {
      const c = new McpClient();
      await c.connect("hol4-mcp", ["--transport", "stdio"]);
      client = c;
      return c;
    })();

    try {
      return await connecting;
    } finally {
      connecting = null;
    }
  }

  async function cleanup() {
    client?.close();
    client = null;
  }

  async function registerMcpTools() {
    if (toolsRegistered) return;

    const mcpClient = await getClient();
    const { tools } = await mcpClient.listTools();

    for (const tool of tools) {
      const inputSchema = tool.inputSchema || { type: "object", properties: {} };
      const parameters = jsonSchemaToTypebox(inputSchema);

      pi.registerTool({
        name: tool.name,
        label: tool.name.replace(/_/g, " ").replace(/\b\w/g, (c) => c.toUpperCase()),
        description: tool.description || `MCP tool: ${tool.name}`,
        parameters,

        async execute(toolCallId, params, onUpdate, ctx, signal) {
          try {
            const mcpClient = await getClient();

            if (signal?.aborted) {
              return { content: [{ type: "text", text: "Cancelled" }], details: {}, isError: true };
            }

            const result = await mcpClient.callTool(tool.name, params as Record<string, unknown>);

            const textContent = result.content
              .filter((c): c is { type: "text"; text: string } => c.type === "text" && typeof c.text === "string")
              .map((c) => c.text)
              .join("\n");

            return {
              content: [{ type: "text", text: textContent || "(no output)" }],
              details: { mcpResult: result },
              isError: result.isError === true,
            };
          } catch (err) {
            const message = err instanceof Error ? err.message : String(err);
            return { content: [{ type: "text", text: `MCP error: ${message}` }], details: {}, isError: true };
          }
        },
      });
    }

    toolsRegistered = true;
  }

  pi.on("session_start", async () => {
    try {
      await registerMcpTools();
    } catch (err) {
      console.error(`HOL4 MCP init failed: ${err instanceof Error ? err.message : err}`);
    }
  });

  pi.on("session_shutdown", async () => {
    await cleanup();
  });
}
