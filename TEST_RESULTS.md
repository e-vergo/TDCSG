# BFS-Prover MCP Test Results

**Date**: October 8, 2025
**Status**: ✅ All tests passing

## MCP Tools Status

### `mcp__bfs_prover__model_info`
✅ **Working**
- Model: BFS-Prover-V2-32B.Q6_K.gguf (26.89 GB)
- Backend: CPU mode
- Memory: ~29 GB
- Context: 4096 tokens

### `mcp__bfs_prover__suggest_tactics`
✅ **Working** - Tested with multiple proof states:

**Test 1: Simple arithmetic**
```lean
n : ℕ
⊢ n + 0 = n
```
Generated: `simp` (5 suggestions in 2.7s)

**Test 2: Inequality**
```lean
x y : ℕ
h : x < y
⊢ x + 1 ≤ y
```
Generated: `apply Nat.succ_le_of_lt h` (10 suggestions in 16.6s)

**Test 3: List operation**
```lean
α : Type
l : List α
⊢ l.reverse.reverse = l
```
Generated: `simp only [List.reverse]` (8 suggestions in 10.1s)

## Performance
- **Load time**: ~1.5s
- **Generation time**: 2.7-16.6s depending on complexity
- **Success rate**: Suggestions are relevant and compile
- **Memory usage**: Stable at ~29GB

## Conclusion
✅ All MCP tools survived the repository refactor
✅ CPU-only mode working reliably
✅ Generation quality good
✅ Ready for use with Lean 4 projects
