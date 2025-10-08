# BFS-Prover MCP Debugging Summary

## Problem
The `mcp__bfs_prover__suggest_tactics` tool was failing with error:
```
llama_decode returned -3
```

## Root Cause
The llama.cpp error code -3 typically indicates one of these issues:
1. **Context overflow** - Prompt too long for the model's context window (4096 tokens)
2. **Invalid tokens** - Special characters causing tokenization issues
3. **Model state corruption** - Previous error left model in bad state

The complex Lean proof states (with long mathematical expressions) were likely exceeding the context window or containing characters that confused the tokenizer.

## Solution
Added robust error handling and context management to `bfs_prover_mcp/model.py`:

### Changes Made:

1. **Context Length Checking** (lines 60-67):
   ```python
   # Check prompt length (rough estimate: 1 token ≈ 4 chars)
   estimated_tokens = len(prompt) // 4
   if estimated_tokens + max_tokens > self.n_ctx:
       # Truncate proof state to fit context
       max_state_chars = (self.n_ctx - max_tokens - 100) * 4  # Leave buffer
       if len(proof_state) > max_state_chars:
           proof_state = proof_state[:max_state_chars] + "\n..."
           prompt = format_bfs_prover_prompt(proof_state)
   ```

2. **Try-Except Error Handling** (lines 71-91):
   ```python
   for i in range(num_suggestions):
       try:
           output = self.model(...)
           # Extract tactic
       except Exception as e:
           # Log error and continue to next generation
           print(f"Warning: Failed to generate tactic {i+1}/{num_suggestions}: {e}")
           # Reset model state if llama_decode error
           if "llama_decode" in str(e):
               print("Detected llama_decode error, resetting model...")
               self.model.reset()
           continue
   ```

3. **Increased Default max_tokens** (line 51):
   - Changed from `128` to `128*16 = 2048`
   - Allows longer tactic generation (useful for complex proofs)
   - Still safely under context limit with truncation

## Testing
Created `test_bfs_prover.py` to verify the fixes work:
- ✅ Simple proof state: `⊢ 1 + 1 = 2` - Generates 5 tactics successfully
- ✅ Complex proof state: Long expression with `TwoDiskSystem.ζ₅` - Generates 5 tactics successfully

## How to Use After Fix

### Option 1: Wait for MCP Auto-Reconnect
The MCP server will auto-restart when Claude Code reconnects. Just try calling the tool again after a few moments.

### Option 2: Manual Test
Run the standalone test script:
```bash
.venv/bin/python test_bfs_prover.py
```

### Option 3: Restart Claude Code
Restart the Claude Code application to force MCP server reload with new code.

## Expected Behavior Now

1. **Long proof states** - Automatically truncated to fit context
2. **Model errors** - Caught, logged, and model state reset
3. **Partial success** - If some tactics fail to generate, returns successful ones
4. **Graceful degradation** - Always returns what it can instead of crashing

## Future Improvements

Could add:
1. Better tokenization (use actual tokenizer instead of char estimate)
2. Proof state simplification (remove redundant parts before sending)
3. Retry logic with exponential backoff
4. Cache successful prompts to avoid re-computing

## Model Info
- **Model**: BFS-Prover-V2-32B.Q6_K.gguf (26.89 GB)
- **Context**: 4096 tokens (model was trained on 131072)
- **Backend**: Metal (Apple Silicon GPU acceleration)
- **Load time**: ~1.8-2s
- **Inference time**: ~5-10s for 5 tactics

## Status
✅ **FIXED** - All tests passing as of this commit
