"""BFS-Prover MCP Server - Main entry point."""

import asyncio
import logging
import os
from pathlib import Path
from typing import Any, Optional, Sequence

from mcp.server import Server
from mcp.types import Tool, TextContent
import mcp.server.stdio
from pydantic import BaseModel, Field

from .model import BFSProverModel

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Input models for validation
class SuggestTacticsInput(BaseModel):
    proof_state: str = Field(..., description="Lean proof state")
    num_suggestions: int = Field(5, ge=1, le=20)
    temperature: float = Field(0.7, ge=0.0, le=2.0)
    max_tokens: int = Field(128, ge=16, le=512)


class ReloadModelInput(BaseModel):
    model_path: Optional[str] = None


# Global model instance
_model: Optional[BFSProverModel] = None


def get_model() -> BFSProverModel:
    """Get the global model instance."""
    if _model is None:
        raise RuntimeError("Model not initialized")
    return _model


async def initialize_model(model_path: str | Path) -> None:
    """Initialize the model at server startup."""
    global _model

    logger.info(f"Loading BFS-Prover model from {model_path}")
    _model = BFSProverModel(model_path=model_path)

    # Load in thread pool to avoid blocking
    loop = asyncio.get_event_loop()
    await loop.run_in_executor(None, _model.load)

    logger.info(f"Model loaded in {_model.load_time:.2f}s")


# MCP Server
app = Server("bfs-prover-mcp")


@app.list_tools()
async def list_tools() -> list[Tool]:
    """List available MCP tools."""
    return [
        Tool(
            name="suggest_tactics",
            description="Generate Lean 4 tactic suggestions for a proof state",
            inputSchema={
                "type": "object",
                "properties": {
                    "proof_state": {
                        "type": "string",
                        "description": "Lean proof state with hypotheses and goals",
                    },
                    "num_suggestions": {
                        "type": "integer",
                        "description": "Number of tactics to generate (1-20)",
                        "default": 5,
                    },
                    "temperature": {
                        "type": "number",
                        "description": "Sampling temperature (0.0-2.0)",
                        "default": 0.7,
                    },
                    "max_tokens": {
                        "type": "integer",
                        "description": "Max tokens per tactic (16-512)",
                        "default": 128,
                    },
                },
                "required": ["proof_state"],
            },
        ),
        Tool(
            name="model_info",
            description="Get information about the loaded model",
            inputSchema={"type": "object", "properties": {}},
        ),
        Tool(
            name="reload_model",
            description="Reload the model (use after errors or to switch models)",
            inputSchema={
                "type": "object",
                "properties": {
                    "model_path": {
                        "type": "string",
                        "description": "Optional new model path",
                    }
                },
            },
        ),
    ]


@app.call_tool()
async def call_tool(name: str, arguments: Any) -> Sequence[TextContent]:
    """Handle tool calls."""

    if name == "suggest_tactics":
        # Validate input
        input_data = SuggestTacticsInput(**arguments)

        # Generate tactics in thread pool
        model = get_model()
        loop = asyncio.get_event_loop()

        start_time = loop.time()
        tactics = await loop.run_in_executor(
            None,
            model.generate_tactics,
            input_data.proof_state,
            input_data.num_suggestions,
            input_data.temperature,
            input_data.max_tokens,
        )
        generation_time = (loop.time() - start_time) * 1000

        # Format response as simple numbered list
        response_lines = [
            f"Generated {len(tactics)} tactic suggestions in {generation_time:.0f}ms:",
            "",
        ]
        for i, tactic in enumerate(tactics, 1):
            response_lines.append(f"{i}. {tactic}")

        response_lines.append("")
        response_lines.append(
            "💡 Test these with mcp__lean_lsp__lean_multi_attempt to see which ones work!"
        )

        return [TextContent(type="text", text="\n".join(response_lines))]

    elif name == "model_info":
        model = get_model()
        info = model.get_info()

        # Format info nicely
        lines = [
            "BFS-Prover Model Info:",
            f"  Model: {info['model_name']}",
            f"  Size: {info['model_size_gb']:.2f} GB",
            f"  Loaded: {info['model_loaded']}",
            f"  Context: {info['context_length']} tokens",
            f"  Memory: {info['memory_usage_gb']:.2f} GB",
            f"  Backend: {info['backend']}",
            f"  Uptime: {info['uptime_seconds']:.0f}s",
        ]

        return [TextContent(type="text", text="\n".join(lines))]

    elif name == "reload_model":
        input_data = ReloadModelInput(**arguments)
        model = get_model()

        loop = asyncio.get_event_loop()
        load_time = await loop.run_in_executor(
            None, model.reload, Path(input_data.model_path) if input_data.model_path else None
        )

        result = f"✓ Model reloaded successfully in {load_time:.2f}s"

        return [TextContent(type="text", text=result)]

    else:
        raise ValueError(f"Unknown tool: {name}")


async def main():
    """Main entry point for the MCP server."""
    # Get model path from environment or default
    model_path = os.getenv(
        "BFS_PROVER_MODEL_PATH", "./models/BFS-Prover-V2-32B-GGUF/model.gguf"
    )

    # Initialize model
    await initialize_model(model_path)

    # Run server
    async with mcp.server.stdio.stdio_server() as (read_stream, write_stream):
        await app.run(read_stream, write_stream, app.create_initialization_options())


if __name__ == "__main__":
    asyncio.run(main())
