#!/usr/bin/env python3
"""
BFS-Prover MCP Server

Model Context Protocol server exposing BFS-Prover tactic generation as tools.
Follows the architecture specified in mcp_spec.txt.
"""

import asyncio
import os
from typing import Any, Sequence

from mcp.server import Server
from mcp.types import Tool, TextContent
import mcp.server.stdio

from .client import DaemonClient


# Initialize MCP server
app = Server("bfs-prover-mcp")

# Initialize daemon client
client = DaemonClient(
    host=os.getenv("TACTIC_SERVER_HOST", "localhost"),
    port=int(os.getenv("TACTIC_SERVER_PORT", "5678")),
    timeout=int(os.getenv("TACTIC_SERVER_TIMEOUT", "30"))
)


@app.list_tools()
async def list_tools() -> list[Tool]:
    """List available tools."""
    return [
        Tool(
            name="bfs_suggest_tactics",
            description="Generate Lean 4 tactic suggestions for a proof state using BFS-Prover",
            inputSchema={
                "type": "object",
                "properties": {
                    "proof_state": {
                        "type": "string",
                        "description": "The proof state from lean_goal tool"
                    },
                    "num_suggestions": {
                        "type": "integer",
                        "description": "Number of tactic suggestions to generate (1-10)",
                        "default": 5,
                        "minimum": 1,
                        "maximum": 10
                    },
                    "temperature": {
                        "type": "number",
                        "description": "Sampling temperature (0.0-1.0, higher = more creative)",
                        "default": 0.7,
                        "minimum": 0.0,
                        "maximum": 1.0
                    },
                    "max_tokens": {
                        "type": "integer",
                        "description": "Maximum tokens per tactic (16-512)",
                        "default": 128,
                        "minimum": 16,
                        "maximum": 512
                    }
                },
                "required": ["proof_state"]
            }
        ),
        Tool(
            name="bfs_daemon_status",
            description="Check if the BFS-Prover daemon is running and responsive",
            inputSchema={
                "type": "object",
                "properties": {},
                "required": []
            }
        )
    ]


@app.call_tool()
async def call_tool(name: str, arguments: Any) -> Sequence[TextContent]:
    """Handle tool calls."""

    if name == "bfs_daemon_status":
        try:
            status = client.get_daemon_status()
            return [
                TextContent(
                    type="text",
                    text=format_status_response(status)
                )
            ]
        except Exception as e:
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "error",
                        str(e),
                        "Check if daemon is running with './tactic_server.sh status'"
                    )
                )
            ]

    elif name == "bfs_suggest_tactics":
        proof_state = arguments.get("proof_state", "")
        num_suggestions = arguments.get("num_suggestions", 5)
        temperature = arguments.get("temperature", 0.7)
        max_tokens = arguments.get("max_tokens", 128)

        # Validate inputs
        if not proof_state or not proof_state.strip():
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "invalid_input",
                        "Proof state cannot be empty",
                        "Use mcp__lean-lsp__lean_goal to get a proof state first"
                    )
                )
            ]

        if not (1 <= num_suggestions <= 10):
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "invalid_input",
                        f"num_suggestions must be between 1 and 10, got {num_suggestions}",
                        "Use a value between 1 and 10"
                    )
                )
            ]

        if not (0.0 <= temperature <= 1.0):
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "invalid_input",
                        f"temperature must be between 0.0 and 1.0, got {temperature}",
                        "Use a value between 0.0 (deterministic) and 1.0 (creative)"
                    )
                )
            ]

        if not (16 <= max_tokens <= 512):
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "invalid_input",
                        f"max_tokens must be between 16 and 512, got {max_tokens}",
                        "Use a value between 16 and 512"
                    )
                )
            ]

        try:
            result = client.generate_tactics(
                proof_state=proof_state,
                num_suggestions=num_suggestions,
                temperature=temperature,
                max_tokens=max_tokens
            )

            return [
                TextContent(
                    type="text",
                    text=format_tactics_response(result)
                )
            ]

        except ConnectionRefusedError as e:
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "daemon_not_running",
                        str(e),
                        "Run './tactic_server.sh start' to start the daemon"
                    )
                )
            ]
        except TimeoutError as e:
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "timeout",
                        str(e),
                        "Try './tactic_server.sh restart' to restart the daemon"
                    )
                )
            ]
        except ValueError as e:
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "invalid_input",
                        str(e),
                        "Check that all parameters are within valid ranges"
                    )
                )
            ]
        except Exception as e:
            return [
                TextContent(
                    type="text",
                    text=format_error_response(
                        "unknown_error",
                        str(e),
                        "Check '.tactic_server.log' for details or restart daemon"
                    )
                )
            ]

    else:
        return [
            TextContent(
                type="text",
                text=f"Unknown tool: {name}"
            )
        ]


def format_status_response(status: dict) -> str:
    """Format daemon status response."""
    lines = [
        "BFS-Prover Daemon Status:",
        f"  Status: {status['status']}",
        f"  Port: {status['port']}",
        f"  PID: {status.get('pid', 'N/A')}",
        f"  Model Loaded: {status.get('model_loaded', False)}"
    ]

    if status['status'] == 'stopped':
        lines.append("")
        lines.append("ℹ To start: ./tactic_server.sh start")
    elif status['status'] == 'unresponsive':
        lines.append("")
        lines.append("⚠ Daemon may be stuck. Try: ./tactic_server.sh restart")

    return "\n".join(lines)


def format_tactics_response(result: dict) -> str:
    """Format tactics generation response."""
    tactics = result.get('tactics', [])
    elapsed = result.get('time', 0)

    lines = [
        f"Generated {len(tactics)} tactic suggestions in {elapsed:.1f}s:",
        ""
    ]

    for i, tactic in enumerate(tactics, 1):
        lines.append(f"{i}. {tactic}")

    lines.append("")
    lines.append("💡 Test these with lean_multi_attempt to see which ones work!")

    return "\n".join(lines)


def format_error_response(error_type: str, message: str, suggestion: str) -> str:
    """Format error response with helpful suggestions."""
    return f"""Error: {error_type}

{message}

Suggestion: {suggestion}"""


async def main():
    """Run the MCP server."""
    async with mcp.server.stdio.stdio_server() as (read_stream, write_stream):
        await app.run(
            read_stream,
            write_stream,
            app.create_initialization_options()
        )


if __name__ == "__main__":
    asyncio.run(main())
