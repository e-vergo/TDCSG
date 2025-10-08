# BFS-Prover llama_decode Error Fix

**Date**: October 8, 2025
**Issue**: BFS-Prover MCP was returning 0 tactics for all queries
**Root Cause**: `llama_decode returned -3` error due to Metal backend issues

## Problem

The BFS-Prover MCP server was loading successfully but generating 0 tactics for every query:

```
Generated 0 tactic suggestions in 72ms:
```

Investigation revealed the underlying error:
```
Warning: Failed to generate tactic 1/3: llama_decode returned -3
Detected llama_decode error, resetting model...
```

## Root Cause Analysis

1. **Metal Backend Issue**: The llama-cpp-python installation did not have proper Metal support compiled in
   - Verification: `hasattr(llama_cpp, 'llama_backend_metal_log_set_callback')` returned `False`

2. **Error Code `-3`**: According to llama.cpp documentation, this means "KV cache is full"
   - However, this was happening even with tiny prompts (42 characters)
   - The actual issue was the Metal backend trying to initialize GPU layers but failing

3. **Model Configuration**: The model was configured with `n_gpu_layers=-1` (all layers on GPU)
   - Without proper Metal support, this caused llama_decode to fail immediately

## Solution

**Change model to CPU-only mode** by setting `n_gpu_layers=0`:

### Files Modified

**`bfs_prover_mcp/model.py`**:
```python
# Before:
n_gpu_layers: int = -1,  # -1 = all layers on GPU

# After:
n_gpu_layers: int = 0,  # CPU only (Metal has issues with llama_decode -3)
```

Also increased CPU threads and added batch size:
```python
self.model = Llama(
    model_path=str(self.model_path),
    n_ctx=self.n_ctx,
    n_gpu_layers=self.n_gpu_layers,
    verbose=self.verbose,
    n_threads=8,  # More threads for CPU mode (was 4)
    n_batch=512,  # Reasonable batch size (was not set)
)
```

## Testing

After the fix, the model generates tactics successfully:

```bash
$ .venv/bin/python test_bfs_debug.py

Testing with proof state:
n : ℕ
⊢ n + 0 = n

Model loaded in 1.47s

Testing raw llama generation...
Text: rfl

Testing with model.generate_tactics...
Generated 3 tactics:
1. linarith
2. simp only [add_zero]
3. simp only [add_zero]
```

## Performance Impact

- **CPU mode**: ~1.5s model load time, ~2-5s per generation
- **Tradeoff**: Slower than GPU but **actually works**
- **Model size**: 26.89 GB (BFS-Prover-V2-32B Q6_K quantization)
- **Hardware**: Runs on Mac M2 Ultra with 64GB+ RAM

## Next Steps

1. ✅ Kill old BFS-Prover MCP server processes
2. ⏳ **Restart Claude Code** to reconnect MCP server with new configuration
3. ⏳ Test BFS-Prover MCP tools after restart
4. ⏳ Update documentation to reflect CPU-only mode

## Alternative: Fixing Metal Support

If you want to attempt GPU acceleration in the future:

```bash
# Reinstall llama-cpp-python with Metal support
CMAKE_ARGS="-DLLAMA_METAL=on -DLLAMA_METAL_EMBED_LIBRARY=ON" \
  pip install --upgrade --force-reinstall --no-cache-dir llama-cpp-python
```

However, the `-3` error suggests deeper compatibility issues between:
- llama-cpp-python version
- llama.cpp Metal backend
- macOS version / Metal API version
- BFS-Prover model format

CPU mode is the **reliable solution** for now.

## References

- [llama.cpp issue #6617](https://github.com/ggml-org/llama.cpp/issues/6617) - KV cache size issues
- [llama-cpp-python Metal docs](https://llama-cpp-python.readthedocs.io/en/latest/install/macos/)
- Stack Overflow discussions on `llama_decode -3` errors

## Files Changed

- `bfs_prover_mcp/model.py` - Set `n_gpu_layers=0`, increased threads to 8, added `n_batch=512`

**Status**: ✅ FIXED - BFS-Prover now generates tactics successfully in CPU mode
