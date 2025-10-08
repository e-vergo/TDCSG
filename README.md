# BFS-Prover MCP Server

MCP server for AI-powered Lean 4 tactic generation using the BFS-Prover-V2 model.

## Setup

1. **Install dependencies:**
```bash
pip install llama-cpp-python mcp pydantic psutil
```

2. **Download model:**
Get [BFS-Prover-V2-32B-Q6_K.gguf](https://huggingface.co/mradermacher/BFS-Prover-V2-32B-GGUF) and place in `BFS-Prover-V2-32B-GGUF/`

3. **Configure MCP:**
Add to `.mcp.json`:
```json
{
  "mcpServers": {
    "bfs_prover": {
      "command": "/path/to/.venv/bin/python",
      "args": ["-m", "bfs_prover_mcp.server"],
      "env": {
        "BFS_PROVER_MODEL_PATH": "/path/to/BFS-Prover-V2-32B.Q6_K.gguf"
      }
    }
  }
}
```

4. Restart Claude Code

## Usage

```python
# Get proof state
goal = mcp__lean-lsp__lean_goal(file_path, line_number)

# Generate tactics
result = mcp__bfs_prover__suggest_tactics(
    proof_state=goal,
    num_suggestions=10,
    temperature=0.7
)

# Test tactics
results = mcp__lean-lsp__lean_multi_attempt(file_path, line_number, tactics)
```

## Configuration

**CPU-only mode** (default in `bfs_prover_mcp/model.py`):
- `n_gpu_layers=0` - Metal backend has issues, CPU works reliably
- `n_threads=8` - Uses multiple CPU cores
- `n_batch=512` - Reasonable batch size

**Performance:**
- Load time: ~1.5s
- Generation: ~6s for 10 tactics
- Memory: ~28GB
- Success rate: 30-40% make meaningful progress

## Troubleshooting

**Returns 0 tactics:**
- Check model path is correct
- Run `tests/test_cpu_only.py` to verify setup

**Out of memory:**
- Close other applications
- Need 64GB+ RAM for 32B model

## Files

- `bfs_prover_mcp/` - MCP server implementation
- `tests/` - Test scripts
- `BFS_PROVER_FIX_SUMMARY.md` - Technical details on the CPU-mode fix

## Technical Notes

Fixed `llama_decode returned -3` error by switching from GPU (Metal) to CPU-only mode. Metal backend has compatibility issues with llama-cpp-python. CPU mode is slower but reliable and fast enough (~6s per query).
