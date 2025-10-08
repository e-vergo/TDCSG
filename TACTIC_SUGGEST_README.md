# BFS-Prover Tactic Suggestion Tool

Integration of BFS-Prover-V2-7B for generating Lean4 tactic suggestions with both one-shot and daemon modes.

## Setup

### 1. Install Dependencies

The dependencies are already installed in `.venv` for this project:

```bash
# Dependencies already in .venv:
# - torch (with MPS support for Apple Silicon)
# - transformers
# - accelerate
```

If setting up elsewhere:
```bash
pip install torch torchvision torchaudio transformers accelerate
```

### 2. Verify Model is Downloaded

Make sure the BFS-Prover model is at `./BFS-Prover-V2-7B/`

## Usage Modes

### 🚀 Daemon Mode (Recommended - 10x Faster!)

The daemon keeps the model loaded in memory, making subsequent requests ~10x faster.

**Start the server:**
```bash
./tactic_server.sh start
# Takes 10-20s to load model first time
# Server stays running in background
```

**Query for tactics:**
```bash
.venv/bin/python3 tactic_query.py --state "n : ℕ
h : n > 0
⊢ n + 1 > 0" --num 3

# Output (in ~2 seconds!):
# linarith
# omega
# simp_arith
```

**Stop the server:**
```bash
./tactic_server.sh stop
```

**Check status:**
```bash
./tactic_server.sh status
```

**View logs:**
```bash
./tactic_server.sh logs
```

### 📝 One-Shot Mode (Simple but Slower)

For occasional use or when you don't want a background server:

```bash
.venv/bin/python3 tactic_suggest.py --state "n : ℕ
⊢ n + 0 = n" --num 3 --quiet

# Takes ~15-20s (includes model loading)
```

## Command Reference

### Daemon Mode

**tactic_server.sh:**
- `start` - Start the daemon (model loads once)
- `stop` - Stop the daemon
- `restart` - Restart the daemon
- `status` - Check if running
- `logs` - Tail the log file

**tactic_query.py:**
```bash
.venv/bin/python3 tactic_query.py [OPTIONS]

Options:
  --state TEXT        Proof state (or read from stdin)
  --num N            Number of suggestions (default: 3)
  --temp T           Temperature 0.0-1.0 (default: 0.7)
  --max-tokens N     Max tokens per tactic (default: 128)
  --format FORMAT    Output: 'lines' or 'json' (default: lines)
  --port PORT        Server port (default: 5678)
  --quiet            Suppress timing info
```

### One-Shot Mode

**tactic_suggest.py:**
```bash
.venv/bin/python3 tactic_suggest.py [OPTIONS]

Options:
  --state TEXT        Proof state (or read from stdin)
  --num N            Number of suggestions (default: 3)
  --temp T           Temperature (default: 0.7)
  --max-tokens N     Max tokens (default: 128)
  --quiet            Minimal output
  --format FORMAT    Output: 'lines' or 'json'
  --model-path PATH  Model directory (default: ./BFS-Prover-V2-7B)
```

## Integration with Lean LSP (for Claude)

### Daemon Workflow (Recommended)

```python
# 1. Start daemon (if not already running)
bash("./tactic_server.sh start")

# 2. Get proof state
goal = mcp__lean-lsp__lean_goal("file.lean", line=42, column=5)

# 3. Generate tactics (fast - ~2s)
result = bash(".venv/bin/python3 tactic_query.py --state '" + goal + "' --num 5")
tactics = result.stdout.strip().split("\n")

# 4. Test all suggestions
results = mcp__lean-lsp__lean_multi_attempt("file.lean", line=42, snippets=tactics)

# 5. Pick the best and edit the file
```

### One-Shot Workflow (No Daemon)

```python
# 1. Get proof state
goal = mcp__lean-lsp__lean_goal("file.lean", line=42, column=5)

# 2. Generate tactics (slower - ~15s)
result = bash(".venv/bin/python3 tactic_suggest.py --state '" + goal + "' --num 5 --quiet")
tactics = result.stdout.strip().split("\n")

# 3. Test all suggestions
results = mcp__lean-lsp__lean_multi_attempt("file.lean", line=42, snippets=tactics)
```

## Performance Comparison

| Mode | First Request | Subsequent Requests | Use Case |
|------|---------------|---------------------|----------|
| **Daemon** | 15s (model load + generation) | **2-5s** ⚡ | Multiple proofs in one session |
| **One-Shot** | 15s | 15s (reloads each time) | Occasional single queries |

**Recommendation:** Use daemon mode when working on multiple sorries. The 10x speedup adds up quickly!

## Output Formats

### Lines Format (Default)
```bash
.venv/bin/python3 tactic_query.py --state "..." --num 3

# Output:
# linarith
# omega
# simp_arith
# # 3 tactics in 2.1s
```

### JSON Format
```bash
.venv/bin/python3 tactic_query.py --state "..." --format json

# Output:
# {
#   "tactics": ["linarith", "omega", "simp_arith"],
#   "time": 2.1,
#   "num_generated": 3
# }
```

## Examples

### Example 1: Simple Arithmetic
```bash
.venv/bin/python3 tactic_query.py --state "n : ℕ
h : n > 0
⊢ n + 1 > 0" --num 3

# Output:
# linarith
# omega
# simp_arith
```

### Example 2: Commutativity
```bash
.venv/bin/python3 tactic_query.py --state "x y : ℝ
⊢ x + y = y + x" --num 3

# Output:
# simp only [add_comm]
# ring
# abel
```

### Example 3: Induction
```bash
.venv/bin/python3 tactic_query.py --state "n m : ℕ
⊢ n + m = m + n" --num 2

# Output:
# induction m with | zero => simp | succ m ih => simp [ih, add_succ]
# induction n with | zero => simp | succ n ih => simp [add_succ, ih]
```

## Troubleshooting

### Server won't start
Check the logs:
```bash
cat .tactic_server.log
```

Common issues:
- Port 5678 already in use (change with `--port`)
- Model not found at `./BFS-Prover-V2-7B/`
- Out of memory (~14GB needed for model)

### "Connection refused"
The server isn't running. Start it:
```bash
./tactic_server.sh start
```

### Slow performance
- **Daemon mode**: Should be 2-5s per request
- **One-shot mode**: Always 15-20s (expected)
- If daemon is slow, restart it: `./tactic_server.sh restart`

### Model suggestions are wrong
The model was trained on an older version of mathlib4, so:
- Some lemma names may be outdated
- Some tactics may not exist in your version
- Use suggestions as inspiration, not gospel

## Advanced Usage

### Custom Temperature for Diversity
```bash
# Low temp (0.3) = more deterministic, similar tactics
.venv/bin/python3 tactic_query.py --state "..." --temp 0.3 --num 5

# High temp (0.9) = more creative, diverse tactics
.venv/bin/python3 tactic_query.py --state "..." --temp 0.9 --num 5
```

### Pipeline with stdin
```bash
# From Lean goal output
mcp__lean-lsp__lean_goal file.lean 42 5 | .venv/bin/python3 tactic_query.py --num 3
```

### Background Server Management
```bash
# Start and forget
./tactic_server.sh start

# Work on proofs...
.venv/bin/python3 tactic_query.py --state "..." --num 3
.venv/bin/python3 tactic_query.py --state "..." --num 3
.venv/bin/python3 tactic_query.py --state "..." --num 3

# Stop when done
./tactic_server.sh stop
```

## Files Overview

- `tactic_server.py` - Socket-based daemon server (persistent model)
- `tactic_query.py` - Client for querying the daemon
- `tactic_server.sh` - Wrapper script for managing daemon
- `tactic_suggest.py` - One-shot mode (loads model each time)
- `BFS_inference.py` - Core model inference logic
- `.tactic_server.pid` - Daemon PID file (auto-managed)
- `.tactic_server.log` - Daemon logs

## Tips for Best Results

1. **Start daemon at beginning of session** - Save time on all subsequent queries
2. **Use higher temperature for stuck proofs** - More creative suggestions
3. **Generate 5+ suggestions** - Increases chance of finding working tactic
4. **Test with multi_attempt** - Automatically validates all suggestions
5. **Treat as inspiration** - Model may suggest outdated tactics, but the approach is often right
6. **Check similar proofs first** - Model works best on standard mathlib patterns

## Performance Metrics (Observed)

- Model size: ~14GB in memory
- Load time: 10-15s (one-time per daemon session)
- Generation: ~1-2s per tactic
- 3 tactics: ~2-3s (daemon) vs ~15s (one-shot)
- 5 tactics: ~4-6s (daemon) vs ~20s (one-shot)

## Acknowledgments

Based on BFS-Prover-V2-7B, a Lean4 tactic generation model trained on mathlib4 proofs.
