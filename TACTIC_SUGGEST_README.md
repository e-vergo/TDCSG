# BFS-Prover Tactic Suggestion Tool

Integration of BFS-Prover-V2-7B for generating Lean4 tactic suggestions with both one-shot and daemon modes.

## Table of Contents
- [Setup](#setup)
- [Quick Start](#quick-start)
- [Usage Modes](#usage-modes)
- [Command Reference](#command-reference)
- [Examples](#examples)
- [Integration with Claude/Lean LSP](#integration-with-claudelean-lsp)
- [Performance](#performance)
- [Troubleshooting](#troubleshooting)

## Setup

### 1. Dependencies

Dependencies are already installed in `.venv`:
- PyTorch (with MPS support for Apple Silicon)
- Transformers
- Accelerate

For setup elsewhere:
```bash
pip install torch torchvision torchaudio transformers accelerate
```

### 2. Model

Ensure the BFS-Prover model is at `./BFS-Prover-V2-7B/` (~14GB download)

## Quick Start

**Start daemon (recommended for multiple queries):**
```bash
./tactic_server.sh start
```

**Get tactic suggestions:**
```bash
.venv/bin/python3 tactic_query.py --state "n : ℕ
h : n > 0
⊢ n + 1 > 0" --num 3
```

**Output (~2 seconds):**
```
linarith
omega
simp_arith
```

**Stop daemon:**
```bash
./tactic_server.sh stop
```

## Usage Modes

### 🚀 Daemon Mode (Recommended - 10x Faster!)

Keeps the model loaded in memory for fast subsequent requests.

**Manage daemon:**
```bash
./tactic_server.sh start    # Start (loads model once, ~15s)
./tactic_server.sh status   # Check if running
./tactic_server.sh logs     # View logs
./tactic_server.sh restart  # Restart daemon
./tactic_server.sh stop     # Stop daemon
```

**Query daemon:**
```bash
.venv/bin/python3 tactic_query.py --state "PROOF_STATE" --num 5
```

### 📝 One-Shot Mode (Simple but Slower)

For occasional use without a background server:

```bash
.venv/bin/python3 tactic_suggest.py --state "PROOF_STATE" --num 3 --quiet
# Takes ~15-20s (includes model loading each time)
```

## Command Reference

### tactic_server.sh
```bash
./tactic_server.sh {start|stop|restart|status|logs}
```

### tactic_query.py (Daemon Client)
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

### tactic_suggest.py (One-Shot)
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

## Examples

### Simple Arithmetic
```bash
.venv/bin/python3 tactic_query.py --state "n : ℕ
h : n > 0
⊢ n + 1 > 0" --num 3

# Output:
# linarith
# omega
# simp_arith
```

### Commutativity
```bash
.venv/bin/python3 tactic_query.py --state "x y : ℝ
⊢ x + y = y + x" --num 3

# Output:
# simp only [add_comm]
# ring
# abel
```

### Induction
```bash
.venv/bin/python3 tactic_query.py --state "n m : ℕ
⊢ n + m = m + n" --num 2

# Output:
# induction m with | zero => simp | succ m ih => simp [ih, add_succ]
# induction n with | zero => simp | succ n ih => simp [add_succ, ih]
```

### Custom Temperature
```bash
# Deterministic (similar tactics)
.venv/bin/python3 tactic_query.py --state "..." --temp 0.3 --num 5

# Creative (diverse tactics)
.venv/bin/python3 tactic_query.py --state "..." --temp 0.9 --num 5
```

### JSON Output
```bash
.venv/bin/python3 tactic_query.py --state "..." --format json

# Output:
# {
#   "tactics": ["linarith", "omega", "simp_arith"],
#   "time": 2.1,
#   "num_generated": 3
# }
```

## Integration with Claude/Lean LSP

### Daemon Workflow (Recommended)

**Complete workflow for solving a sorry:**

```python
# 1. Start daemon (once per session)
bash("./tactic_server.sh start")

# 2. Get proof state
goal = mcp__lean-lsp__lean_goal("file.lean", line=42, column=5)

# 3. Generate tactics (fast - ~2s)
result = bash(".venv/bin/python3 tactic_query.py --state '" + goal + "' --num 5")
tactics = result.stdout.strip().split("\n")

# 4. Test all suggestions automatically
results = mcp__lean-lsp__lean_multi_attempt("file.lean", line=42, snippets=tactics)

# 5. Analyze results and pick the best
# (Check diagnostics, goal states, etc.)

# 6. Edit file with winning tactic
Edit(file_path="file.lean", old_string="  sorry", new_string="  tactic_here")

# 7. Stop daemon at end of session
bash("./tactic_server.sh stop")
```

### One-Shot Workflow

```python
# 1. Get proof state
goal = mcp__lean-lsp__lean_goal("file.lean", line=42)

# 2. Generate tactics (slower - ~15s)
result = bash(".venv/bin/python3 tactic_suggest.py --state '" + goal + "' --num 5 --quiet")
tactics = result.stdout.strip().split("\n")

# 3. Test all suggestions
results = mcp__lean-lsp__lean_multi_attempt("file.lean", line=42, snippets=tactics)
```

### Multi-Step Proof Iteration

```python
# Start with initial sorry
goal_1 = mcp__lean-lsp__lean_goal("file.lean", line=100)
result_1 = bash(".venv/bin/python3 tactic_query.py --state '" + goal_1 + "'")
# Apply best tactic...

# Get new goal state after first tactic
goal_2 = mcp__lean-lsp__lean_goal("file.lean", line=101)
result_2 = bash(".venv/bin/python3 tactic_query.py --state '" + goal_2 + "'")
# Continue until proof complete
```

### Best Practices for Claude

1. **Start daemon at session start** - Run once, reuse for all queries
2. **Generate 5+ suggestions** - Higher success rate
3. **Use `multi_attempt`** - Test all tactics automatically
4. **Check diagnostics** - Verify tactics compile
5. **Treat as inspiration** - Model may suggest outdated lemmas, but approach is often right
6. **Adjust temperature** - Low (0.5) for simple goals, high (0.9) when stuck
7. **Stop daemon when done** - Frees ~14GB RAM

## Performance

### Comparison Table

| Mode | First Request | Subsequent Requests | Use Case |
|------|---------------|---------------------|----------|
| **Daemon** | 15s (model load + generation) | **2-5s** ⚡ | Multiple proofs in one session |
| **One-Shot** | 15s | 15s (reloads each time) | Occasional single queries |

### Metrics (Observed)

- **Model size:** ~14GB in memory
- **Load time:** 10-15s (one-time per daemon session)
- **Generation:** ~1-2s per tactic
- **3 tactics:** ~2-3s (daemon) vs ~15s (one-shot)
- **5 tactics:** ~4-6s (daemon) vs ~20s (one-shot)

**Recommendation:** Use daemon mode for multiple queries - 10x speedup!

### Success Rates

Based on testing:
- ~50% of tactics compile without errors
- ~20% make actual progress on the proof
- ~0% complete proofs end-to-end (use as brainstorming aid)

### What Works Well

✅ Algebraic manipulations: `ring`, `linarith`, `omega`, `field_simp`
✅ Standard patterns: `constructor`, `induction`, `cases`
✅ Creative witnesses for existentials
✅ Simplification chains: `simp`, `unfold`, `rw`
✅ Breaking down goals with `have` statements

### Known Limitations

⚠️ **Mathlib version mismatch** - Model trained on older mathlib, some lemmas may not exist
⚠️ **No project context** - Doesn't know your custom lemmas/imports
⚠️ **Multi-line tactics** - Sometimes generates tactics `multi_attempt` can't handle
⚠️ **Not always correct** - Use suggestions as inspiration, not gospel

### When to Use

**Good candidates:**
- Standard algebraic/arithmetic proofs
- Induction proofs over lists/nats
- Stuck proofs needing creative approach
- Existential proofs needing concrete witnesses

**Skip for:**
- Custom domain-specific lemmas
- Proofs requiring specific project imports
- Complex multi-step geometric arguments
- Goals with unusual custom structures

## Troubleshooting

### Server won't start
```bash
# Check logs
cat .tactic_server.log

# Common issues:
# - Port 5678 in use (change with --port)
# - Model not found at ./BFS-Prover-V2-7B/
# - Out of memory (~14GB needed)
```

### "Connection refused"
```bash
# Server not running - start it
./tactic_server.sh start
```

### Slow performance
- **Daemon:** Should be 2-5s per request
- **One-shot:** Always 15-20s (expected)
- **If daemon slow:** `./tactic_server.sh restart`

### Model suggestions wrong
The model was trained on older mathlib4:
- Some lemma names outdated
- Some tactics may not exist
- **Use as inspiration, not gospel**

## Files Overview

- `tactic_server.py` - Socket-based daemon server
- `tactic_query.py` - Client for daemon
- `tactic_server.sh` - Management wrapper
- `tactic_suggest.py` - One-shot mode
- `BFS_inference.py` - Core inference logic
- `.tactic_server.pid` - Daemon PID (auto-managed)
- `.tactic_server.log` - Daemon logs

## Tips for Best Results

1. **Start daemon at beginning of session** - Reuse for all queries
2. **Higher temperature for stuck proofs** - More creative suggestions
3. **Generate 5+ suggestions** - Better chance of success
4. **Test with `multi_attempt`** - Automatic validation
5. **Treat as inspiration** - Tactics may be outdated but approach is right
6. **Check similar proofs** - Model works best on standard mathlib patterns

## Example Success Story

**Proof:** `G_on_segment_E'E` in TDCSG project

**Goal:** `∃ t, 0 < t ∧ t < 1 ∧ G = E' + t • (E - E')`

**BFS-Prover suggestions:**
1. `use ((G - E') / (E - E')).re` ✅ **Perfect witness!**
2. `have E_sub_E' : E - E' = 2 * E := by unfold E'; ring` ✅ **Proved automatically!**
3. `constructor` ✅ **Split conjunction correctly!**

**Result:** Structured the proof and made concrete progress!

## Acknowledgments

Based on [BFS-Prover-V2-7B](https://huggingface.co/ByteDance-Seed/BFS-Prover-V2-7B), a Lean4 tactic generation model trained on mathlib4 proofs.
