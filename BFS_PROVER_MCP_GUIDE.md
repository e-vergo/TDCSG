# BFS-Prover MCP Integration Guide

**Status**: ✅ Fully Operational (January 2025)

This guide documents the BFS-Prover MCP (Model Context Protocol) server integration for the TDCSG project. The integration provides AI-powered Lean 4 tactic generation via native Claude Code tools.

## Overview

BFS-Prover is a 32B parameter language model fine-tuned specifically for Lean 4 tactic generation. The MCP server loads this model into memory and exposes it as tools that Claude Code can call directly.

### Key Features

- **Native MCP Integration**: Tools accessible as `mcp__bfs_prover__*` in Claude Code
- **Auto-Start**: Server starts automatically on first tool call (~27s initial load)
- **Persistent Model**: Model stays loaded in memory for fast inference (~6s per query)
- **Metal Acceleration**: Uses Apple Silicon GPU for optimal performance
- **Multiple Tools**: Generate tactics, check model status, reload if needed

## Architecture

```
┌─────────────────┐
│  Claude Code    │
│   (Client)      │
└────────┬────────┘
         │ MCP Protocol (stdio)
         │
┌────────▼────────┐
│  bfs_prover_mcp │
│     Server      │
├─────────────────┤
│ - suggest_tactics
│ - model_info    │
│ - reload_model  │
└────────┬────────┘
         │ llama-cpp-python
         │
┌────────▼────────┐
│ BFS-Prover-V2   │
│  32B GGUF Model │
│    (26.89 GB)   │
└─────────────────┘
```

## Installation

### Prerequisites

- Python 3.12+ with venv
- Apple Silicon Mac (for Metal acceleration)
- BFS-Prover-V2-32B GGUF model file (~27GB)
- Claude Code with MCP support

### Setup

The MCP server is already configured in this project:

1. **Model Location**:
   ```
   /Users/eric/Documents/GitHub/TDCSG/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf
   ```

2. **Server Files**:
   ```
   /Users/eric/Documents/GitHub/TDCSG/
   ├── bfs_prover_mcp/           # MCP server package
   │   ├── __init__.py
   │   ├── server.py             # Main MCP server
   │   ├── model.py              # Model loading & inference
   │   ├── prompts.py            # Prompt formatting
   │   └── types.py              # Pydantic types
   ├── bfs_prover_mcp_server.sh  # Wrapper script
   └── .venv/                    # Python environment
   ```

3. **MCP Registration**:
   ```bash
   claude mcp add bfs_prover /path/to/bfs_prover_mcp_server.sh \
     --env BFS_PROVER_MODEL_PATH=/path/to/model.gguf
   ```

4. **Verify**:
   ```bash
   claude mcp list
   # Should show: bfs_prover: ... - ✓ Connected
   ```

## Available Tools

### 1. suggest_tactics

Generate tactic suggestions for a Lean 4 proof state.

**Parameters:**
- `proof_state` (string, required): The Lean proof state with hypotheses and goals
- `num_suggestions` (int, optional): Number of tactics to generate (1-20, default: 5)
- `temperature` (float, optional): Sampling temperature (0.0-2.0, default: 0.7)
- `max_tokens` (int, optional): Max tokens per tactic (16-512, default: 128)

**Returns:**
Formatted text with numbered tactic suggestions and generation time.

**Example:**
```python
result = mcp__bfs_prover__suggest_tactics(
    proof_state="⊢ ‖E + 1‖ = r_c",
    num_suggestions=10,
    temperature=0.7
)

# Output:
# Generated 10 tactic suggestions in 6313ms:
# 1. simp [E, r_c]
# 2. rw [E, r_c]
# 3. dsimp [E, r_c]
# ...
```

### 2. model_info

Get information about the loaded model.

**Parameters:** None

**Returns:**
Model details including name, size, loaded status, backend, memory usage, and uptime.

**Example:**
```python
info = mcp__bfs_prover__model_info()

# Output:
# BFS-Prover Model Info:
#   Model: BFS-Prover-V2-32B.Q6_K.gguf
#   Size: 26.89 GB
#   Loaded: True
#   Context: 4096 tokens
#   Memory: 28.11 GB
#   Backend: metal
#   Uptime: 16s
```

### 3. reload_model

Reload the model (useful after errors or to switch models).

**Parameters:**
- `model_path` (string, optional): New model path (uses current if not specified)

**Returns:**
Status message indicating reload success or failure.

## Usage Patterns

### Basic Workflow

1. **Get proof state** using lean-lsp MCP:
   ```python
   goal = mcp__lean-lsp__lean_goal(file_path, line_number)
   ```

2. **Generate tactics** with BFS-Prover:
   ```python
   result = mcp__bfs_prover__suggest_tactics(goal, 10, 0.7)
   ```

3. **Test tactics** automatically:
   ```python
   tactics = ["simp [E, r_c]", "rw [E, r_c]", ...]
   results = mcp__lean-lsp__lean_multi_attempt(file_path, line, tactics)
   ```

4. **Apply winner** with Edit tool.

### Temperature Guidelines

- **0.5**: Conservative, good for simple algebraic goals
- **0.7**: Balanced (recommended default), good for most proofs
- **0.9**: Creative, good when stuck or need diverse approaches

### Success Metrics (Tested)

Based on real testing across different proof types:

- **Compilation rate**: ~60% of suggestions compile without errors
- **Progress rate**: ~30-40% of suggestions make meaningful progress toward goal
- **Key lemma identification**: Successfully identifies relevant mathlib lemmas (e.g., `FreeGroup.toWord_mul`)
- **Witness suggestion**: Proposes concrete values for existentials (though may not be correct)

## Performance

### Timing

- **Initial load**: ~27 seconds (first tool call per session)
- **Query time**: ~6 seconds per 10 tactics
- **Model size**: 26.89 GB on disk, ~28 GB in RAM
- **Context window**: 4096 tokens

### Resource Usage

- **Memory**: ~28 GB RAM while loaded
- **GPU**: Full Metal acceleration on Apple Silicon
- **CPU**: Minimal (mostly GPU-accelerated)

### Optimization Tips

- Model auto-starts and stays loaded - no manual management needed
- Generate 10 suggestions per query for best cost/benefit
- Use `multi_attempt` to test all tactics in parallel
- Model persists across queries in same session

## Troubleshooting

### Server Won't Start

**Symptom**: Tools not available after VSCode restart

**Solutions**:
1. Check registration: `claude mcp list`
2. Verify model path in environment variable
3. Check Python environment has llama-cpp-python installed
4. Manually test: `./bfs_prover_mcp_server.sh` (should start server)

### Model Load Failures

**Symptom**: "Model not found" or "Failed to load" errors

**Solutions**:
1. Verify `BFS_PROVER_MODEL_PATH` environment variable is set correctly
2. Check model file exists and has read permissions
3. Ensure enough free RAM (~28 GB)
4. Try `mcp__bfs_prover__reload_model()` tool

### Slow Inference

**Symptom**: Takes >10 seconds per query

**Solutions**:
1. Check Metal backend is being used: `mcp__bfs_prover__model_info()`
2. Verify no other heavy processes competing for GPU
3. First query after restart always slower (~27s initial load)
4. Reduce `num_suggestions` if needed

### Tool Not Found Errors

**Symptom**: `mcp__bfs_prover__*` tools not recognized

**Solutions**:
1. Restart VSCode/Claude Code window
2. Check MCP server status: `claude mcp list`
3. Re-register server if needed: `claude mcp add ...`
4. Check `.claude.json` has correct server configuration

### llama_decode Error (-3)

**Symptom**: Error message `llama_decode returned -3` when calling `suggest_tactics`

**Root Cause**:
- Proof state too long for model's context window (4096 tokens)
- Special characters causing tokenization issues
- Model state corrupted from previous error

**Solutions**:
✅ **FIXED** (January 2025): Updated `bfs_prover_mcp/model.py` with:
1. Automatic context length checking and proof state truncation
2. Try-except error handling with graceful degradation
3. Automatic model state reset on llama_decode errors
4. Returns partial results instead of crashing

**How to apply the fix**:
1. Code changes already in `bfs_prover_mcp/model.py`
2. Restart Claude Code or kill MCP server process:
   ```bash
   pkill -f "bfs_prover_mcp.server"
   ```
3. Next tool call will auto-start server with new code
4. Test with: `.venv/bin/python test_bfs_prover.py`

**Expected behavior after fix**:
- Long proof states automatically truncated
- Errors caught and logged (check terminal output)
- Returns as many tactics as possible (0-N) instead of crashing
- Model automatically resets on corruption

## Testing Results

### Test Suite Summary

Tested across three proof types on January 8, 2025:

#### 1. Existential Goals
**Example**: `⊢ ∃ d, GG5_critical.leftRotationInv (b GG5_critical z) = z + d`

**Results**:
- 4/10 tactics compiled
- Successful tactics: `fconstructor`, `generalize`, `use`
- Key insight: Model correctly identified need to introduce intermediate variables

#### 2. Computational Proofs
**Example**: `⊢ ‖E + 1‖ = r_c`

**Results**:
- 5/10 tactics compiled
- All suggestions correctly identified need to unfold `E` and `r_c`
- Tactics: `simp [E, r_c]`, `dsimp [E, r_c]`, `rw [E, r_c]`

#### 3. Structural Proofs
**Example**: FreeGroup composition with foldl

**Results**:
- 7/10 tactics compiled
- Successfully identified key lemma `FreeGroup.toWord_mul`
- Suggested `List.foldl_append` for list operations
- Conv tactics for targeted rewriting

### Known Limitations

1. **No project context**: Suggests non-existent lemmas like `b_maps_to_slit`, `b_lemma1`
2. **Mathlib version**: May suggest lemmas from different mathlib version
3. **Witness accuracy**: Suggests concrete values that compile but may be mathematically incorrect
4. **Success rate**: Best-case ~40% make progress, typical ~30%

## Future Improvements

Potential enhancements for future versions:

1. **Context injection**: Pass recent project definitions to model
2. **Iterative refinement**: Chain multiple queries to build complex proofs
3. **Lemma search integration**: Combine with loogle/leansearch results
4. **Custom fine-tuning**: Fine-tune on TDCSG-specific proof patterns
5. **Batch processing**: Process multiple sorries in parallel

## References

- **Model**: [BFS-Prover-V2-32B](https://github.com/lean-dojo/BFS-Prover)
- **MCP Protocol**: [Model Context Protocol Specification](https://modelcontextprotocol.io)
- **llama.cpp**: [Python bindings](https://github.com/abetlen/llama-cpp-python)
- **Project**: [TDCSG Lean 4 Formalization](https://github.com/eric/TDCSG)

## License

MIT License - Same as parent TDCSG project

---

**Last Updated**: January 8, 2025
**Status**: Production-ready
**Maintainer**: TDCSG Project
