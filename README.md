# TDCSG - BFS-Prover Tactic Testing System

A daemon-based system for generating and testing Lean 4 tactics using BFS-Prover and lean-lsp.

## Architecture

The system consists of two main components:

1. **Tactic Daemon** (`tactic_daemon.py`): Keeps the BFS-Prover model loaded in memory and serves tactic suggestions via a local socket (port 5678)

2. **Suggest & Test Client** (`suggest_and_test.py`): Requests tactics from the daemon and tests them using lean-lsp MCP's `lean_multi_attempt` tool

## Setup

### Install Dependencies

```bash
python -m venv .venv
source .venv/bin/activate  # or `.venv\Scripts\activate` on Windows
pip install llama-cpp-python
```

### Download BFS-Prover Model

The daemon expects the model at:
```
~/Documents/GitHub/TDCSG/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf
```

Adjust the path in `tactic_daemon.py` if needed.

## Usage

### 1. Start the Tactic Daemon

```bash
python tactic_daemon.py
```

This will:
- Load the BFS-Prover model (~1-2 seconds)
- Listen on `localhost:5678` for tactic requests
- Keep the model in memory for fast inference

### 2. Generate and Test Tactics

```bash
python suggest_and_test.py <file_path> <line_number> <proof_state>
```

Example:
```bash
python suggest_and_test.py \
  /Users/eric/Documents/GitHub/TDCSG/TDCSG/Basic.lean \
  18 \
  "n : ℕ\n⊢ 0 + n = n"
```

This will:
1. Request 10 tactic suggestions from the daemon
2. Test each tactic using lean-lsp MCP
3. Report which tactics succeed

### Example Output

```
================================================================================
BFS-Prover: Suggest and Test
================================================================================
File: /Users/eric/Documents/GitHub/TDCSG/TDCSG/Basic.lean
Line: 18
Proof state:
n : ℕ
⊢ 0 + n = n
================================================================================

Requesting 10 tactics from daemon...
Received 8 tactics

Generated tactics:
  1. apply Nat.zero_add
  2. induction n with\n| zero =>  rfl\n| succ n' ih => rw [add_succ, ih]
  3. simp
  ...

Testing tactics at /Users/eric/Documents/GitHub/TDCSG/TDCSG/Basic.lean:18...
Waiting for lean-lsp response (timeout: 180s)...
Response received, parsing...
================================================================================
TEST RESULTS
================================================================================
✓ SUCCESS: apply Nat.zero_add
✗ FAILED: induction n with...
...

Summary: 1/8 tactics succeeded
```

## Test Scripts

- `test_lean_lsp_simple.py` - Verify lean-lsp MCP starts
- `test_lean_lsp_init.py` - Test MCP initialization
- `test_multi_attempt.py` - Test `lean_multi_attempt` tool directly

## Notes

- **Timeout**: lean-lsp MCP can take 60-90 seconds on first run (building Lean project)
- **Single-line tactics only**: The `lean_multi_attempt` tool requires single-line tactics
- **Model limitations**: BFS-Prover sometimes generates multi-line tactics with `\n` literals that won't work

## Architecture Benefits

1. **Fast inference**: Model stays loaded, ~0.1s per request vs ~2s cold start
2. **Parallel testing**: lean-lsp tests all tactics in parallel
3. **Modular**: Daemon and client are independent
4. **Scalable**: Multiple clients can use the same daemon

## Future Improvements

- Filter multi-line tactics before testing
- Cache lean-lsp connection for faster testing
- Add batch processing mode for multiple proof states
- Implement feedback loop to improve suggestions
