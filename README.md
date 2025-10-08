# BFS-Prover MCP Server

A Model Context Protocol (MCP) server that provides AI-powered Lean 4 tactic generation using the [BFS-Prover-V2 model](https://huggingface.co/ByteDance-Seed/BFS-Prover-V2-32B).

## Overview

This MCP server integrates a locally-running large language model specifically trained on Lean 4 proof tactics, making it available as a tool for AI assistants like Claude Code. It generates tactical suggestions for formal proofs in real-time.

**Key Features:**
- 🤖 **AI Tactic Generation**: Suggests Lean 4 tactics based on proof state
- 🚀 **Fast Inference**: CPU-optimized with ~6s for 10 suggestions
- 🔌 **MCP Integration**: Native integration with Claude Code
- 📦 **Self-Contained**: Runs entirely locally with no external API calls

## Quick Start

### Prerequisites

- Python 3.12+
- 64GB+ RAM recommended (for the 32B model)
- macOS, Linux, or Windows

### Installation

1. **Clone the repository:**
```bash
git clone https://github.com/yourusername/bfs-prover-mcp.git
cd bfs-prover-mcp
```

2. **Create virtual environment:**
```bash
python3 -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate
```

3. **Install dependencies:**
```bash
pip install llama-cpp-python mcp pydantic psutil
```

4. **Download the BFS-Prover model:**

Download one of the quantized GGUF models:
- [BFS-Prover-V2-32B-Q6_K](https://huggingface.co/mradermacher/BFS-Prover-V2-32B-GGUF) (26.89 GB, recommended)
- [BFS-Prover-V2-32B-Q4_K_M](https://huggingface.co/mradermacher/BFS-Prover-V2-32B-GGUF) (19 GB, faster but lower quality)

Place the model file in `BFS-Prover-V2-32B-GGUF/` directory.

5. **Configure MCP in Claude Code:**

Add to your MCP settings (`.mcp.json` or via `claude mcp add`):

```json
{
  "mcpServers": {
    "bfs_prover": {
      "command": "/path/to/bfs-prover-mcp/.venv/bin/python",
      "args": ["-m", "bfs_prover_mcp.server"],
      "env": {
        "BFS_PROVER_MODEL_PATH": "/path/to/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf"
      }
    }
  }
}
```

6. **Restart Claude Code** to load the MCP server.

## Usage

### Basic Workflow

1. **Get proof state** from your Lean file:
```python
goal = mcp__lean-lsp__lean_goal(file_path, line_number)
```

2. **Generate tactics**:
```python
result = mcp__bfs_prover__suggest_tactics(
    proof_state=goal,
    num_suggestions=10,
    temperature=0.7
)
```

3. **Test suggestions** with Lean LSP:
```python
results = mcp__lean-lsp__lean_multi_attempt(file_path, line_number, tactics)
```

4. **Apply the winner** using the Edit tool.

### Example

For a simple Lean proof:
```lean
theorem add_zero (n : ℕ) : n + 0 = n := by
  sorry
```

BFS-Prover might suggest:
1. `rfl`
2. `simp only [add_zero]`
3. `linarith`
4. `ring`

### Available Tools

#### `suggest_tactics`
Generate Lean 4 tactic suggestions for a proof state.

**Parameters:**
- `proof_state` (string): Lean proof state with hypotheses and goals
- `num_suggestions` (int, 1-20): Number of tactics to generate (default: 5)
- `temperature` (float, 0.0-2.0): Sampling temperature (default: 0.7)
- `max_tokens` (int, 16-512): Max tokens per tactic (default: 128)

**Returns:** Numbered list of tactic suggestions

#### `model_info`
Get information about the loaded model (size, backend, memory usage, etc.)

#### `reload_model`
Reload the model, optionally from a new path.

## Architecture

### Components

- **`bfs_prover_mcp/server.py`**: MCP server implementation using FastMCP
- **`bfs_prover_mcp/model.py`**: Model loading and inference with llama-cpp-python
- **`bfs_prover_mcp/prompts.py`**: Prompt formatting for BFS-Prover
- **`test_*.py`**: Test scripts for debugging and validation

### Model Configuration

The server uses **CPU-only mode** by default (`n_gpu_layers=0`) because:
- Metal (GPU) backend has compatibility issues with llama_decode
- CPU mode is reliable and fast enough (~6s for 10 tactics)
- Works consistently across different hardware

**Performance:**
- Model load time: ~1.5s
- Generation time: ~6s for 10 tactics
- Memory usage: ~28 GB

## Troubleshooting

### Common Issues

**1. `llama_decode returned -3` error**

This was the original issue - the model tried to use GPU acceleration but failed. **Solution:** The code now uses CPU-only mode by default (fixed in `model.py`).

**2. Model not generating tactics (returns 0 suggestions)**

- Check that the model file exists and path is correct
- Verify MCP server is running: `mcp__bfs_prover__model_info()`
- Check server logs for errors

**3. Slow generation**

- CPU mode is slower than GPU but more reliable
- Consider using a smaller quantized model (Q4_K_M instead of Q6_K)
- Reduce `num_suggestions` or `max_tokens`

**4. Out of memory**

- The 32B model requires ~28GB RAM
- Try the 7B model version (lower quality but much smaller)
- Close other applications

### Debug Mode

Run test scripts to verify the setup:

```bash
python test_cpu_only.py         # Test basic generation
python test_bfs_debug.py         # Detailed debug output
python test_bfs_prover.py        # Full model test
```

## Documentation

- **[BFS_PROVER_MCP_GUIDE.md](BFS_PROVER_MCP_GUIDE.md)** - Comprehensive usage guide
- **[BFS_PROVER_FIX_SUMMARY.md](BFS_PROVER_FIX_SUMMARY.md)** - Technical details of the CPU-mode fix

## Performance & Benchmarks

Based on testing with real Lean proofs:

- **Success rate**: ~30-40% of suggestions make meaningful progress
- **Compilation rate**: ~60% of suggestions compile without errors
- **Best for**: Standard algebraic proofs, induction, simplification
- **Less effective**: Complex custom domain logic, deep library dependencies

**Example results:**

| Proof Goal | Suggested Tactics | Success |
|------------|------------------|---------|
| `n + 0 = n` | `rfl`, `simp [add_zero]`, `linarith` | ✓ `rfl` solves it |
| `1 - ζ₅ + ζ₅² = ...` | `simp [E, F]`, `field_simp`, `ring` | Partial progress |
| Existential | `use witness`, `constructor`, `fconstructor` | ✓ Made progress |

## Contributing

Contributions welcome! Areas for improvement:

1. **GPU Support**: Fix Metal backend for macOS GPU acceleration
2. **Model Variants**: Support for different BFS-Prover versions
3. **Caching**: Implement tactic suggestion caching
4. **Benchmarks**: Systematic evaluation on mathlib proofs
5. **Documentation**: More examples and use cases

## License

MIT License - see [LICENSE](LICENSE) file.

## References

- [BFS-Prover-V2 Model](https://huggingface.co/ByteDance-Seed/BFS-Prover-V2-32B)
- [Model Context Protocol](https://modelcontextprotocol.io/)
- [llama-cpp-python](https://github.com/abetlen/llama-cpp-python)
- [Lean 4](https://lean-lang.org/)

## Acknowledgments

- **ByteDance-Seed** for training and releasing the BFS-Prover models
- **llama.cpp team** for the inference engine
- **Anthropic** for the Model Context Protocol and Claude Code
