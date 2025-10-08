# Example Workflow: Using BFS-Prover with Lean LSP

This document shows how Claude can integrate the BFS-Prover tactic generator with the existing Lean LSP tools.

## 🚀 Recommended Workflow (with Daemon)

### Setup (Once per session)

**Start the BFS-Prover daemon:**
```bash
./tactic_server.sh start
# Model loads once, stays in memory
# Subsequent queries are 10x faster!
```

### Complete Example: Solving a Sorry

**Scenario:** You have a sorry in `GG5Geometry.lean` at line 150 and want tactic suggestions.

**1. Get the proof state**
```python
# Claude uses MCP tool
goal_output = mcp__lean-lsp__lean_goal(
    file_path="/Users/eric/Documents/GitHub/TDCSG/TDCSG/TwoDisk/GG5Geometry.lean",
    line=150,
    column=3
)
```

**Output example:**
```
φ : ℝ := goldenRatio
r_c : ℝ := Real.sqrt (3 + φ)
E : ℂ := zeta5 - zeta5^2
⊢ ‖E + 1‖ = r_c
```

**2. Generate tactic suggestions (FAST - ~2s)**
```bash
# Claude uses Bash tool with daemon
.venv/bin/python3 tactic_query.py --state "φ : ℝ := goldenRatio
r_c : ℝ := Real.sqrt (3 + φ)
E : ℂ := zeta5 - zeta5^2
⊢ ‖E + 1‖ = r_c" --num 5 --quiet
```

**Output:**
```
unfold E r_c; norm_num; ring_nf
rw [E_def]; simp [zeta5, r_c]; ring
apply norm_eq_sqrt; field_simp; ring
have h := zeta5_and_phi; unfold E; norm_cast
unfold E; rw [add_comm]; simp [norm_add]
```

**3. Test all suggestions automatically**
```python
# Claude uses MCP tool
tactics = [
    "unfold E r_c; norm_num; ring_nf",
    "rw [E_def]; simp [zeta5, r_c]; ring",
    "apply norm_eq_sqrt; field_simp; ring",
    "have h := zeta5_and_phi; unfold E; norm_cast",
    "unfold E; rw [add_comm]; simp [norm_add]"
]

results = mcp__lean-lsp__lean_multi_attempt(
    file_path="/Users/eric/Documents/GitHub/TDCSG/TDCSG/TwoDisk/GG5Geometry.lean",
    line=150,
    snippets=tactics
)
```

**4. Analyze results**

Claude reviews the diagnostics and goal states from each attempt:
- Tactic 1: Error - "unknown identifier 'E_def'"
- Tactic 2: Error - "unknown identifier 'E_def'"
- Tactic 3: Progress - goal changed to subgoal about real numbers
- Tactic 4: Progress - imports zeta5_and_phi fact
- Tactic 5: Error - doesn't simplify

**5. Pick the best and edit**
```python
# Claude uses Edit tool if a tactic worked, or combines the best partial results
Edit(
    file_path="/Users/eric/Documents/GitHub/TDCSG/TDCSG/TwoDisk/GG5Geometry.lean",
    old_string="  sorry",
    new_string="  have h := zeta5_and_phi\n  unfold E\n  sorry  -- Progress: now need to show norm equals r_c using h"
)
```

## Advantages of This Workflow

✅ **Automated testing** - Don't manually try each tactic
✅ **Fast iteration** - Test 5 tactics in one shot
✅ **See all outcomes** - Compare different approaches
✅ **Safe exploration** - MCP tools don't modify files
✅ **Informed decisions** - See exact goal state after each tactic

## Optimization Ideas

### For Repeated Use
If working on many sorries in one session, Claude could:

1. **Cache the goal state extraction** - Save intermediate states
2. **Batch multiple sorries** - Get tactics for several at once
3. **Learn from successes** - Note which tactic patterns work for similar proofs
4. **Temperature adjustment** - Use lower temp (0.5) for simpler goals, higher (0.9) for complex ones

### For Complex Proofs
For proofs needing multiple steps:

1. Get initial goal state
2. Generate first tactic
3. Apply it and get new goal state
4. Generate next tactic for new state
5. Repeat until proven or stuck

## Example: Multi-Step Proof

```python
# Start with initial sorry
goal_1 = lean_goal("file.lean", line=100)
tactics_1 = bash("python3 tactic_suggest.py ...", input=goal_1)

# Simulate applying best tactic
new_line = insert_tactic_at_line_100(tactics_1[0])

# Get new goal state
goal_2 = lean_goal("file.lean", line=101)

# Get next tactic
tactics_2 = bash("python3 tactic_suggest.py ...", input=goal_2)

# Continue until proof complete
```

## Alternative: One-Shot Mode (No Daemon)

If you don't want to manage a background server:

```bash
# Use tactic_suggest.py instead (slower - ~15s per request)
.venv/bin/python3 tactic_suggest.py --state "$goal" --num 5 --quiet
```

**Trade-off:** Simpler but slower - model reloads every time.

## Limitations to Keep in Mind

⚠️ **Mathlib version mismatch** - Model trained on older mathlib, some lemmas may not exist
⚠️ **Context limit** - Very long proof states might need truncation
⚠️ **Tactic format** - Model might generate multi-line tactics (multi_attempt needs single-line)
⚠️ **No project awareness** - Model doesn't know which lemmas are imported in your file
⚠️ **Experimental** - Model may suggest invalid or unhelpful tactics

## When to Use This Tool

**Good candidates:**
- Sorries with clear, simple goals
- Standard algebraic/arithmetic proofs
- Cases where you're stuck and want fresh ideas
- Proofs similar to common mathlib patterns

**Not ideal for:**
- Proofs requiring deep domain knowledge
- Proofs needing specific mathlib lemmas not in training data
- Very long or complex multi-step proofs
- Proofs with unusual custom types/structures

## Best Practices for Claude

1. **Start daemon at session start** - Run `./tactic_server.sh start` once, reuse for all queries
2. **Always check diagnostics** after trying generated tactics
3. **Verify syntax** - Make sure tactics are single-line for multi_attempt
4. **Start conservative** - Try 3-5 suggestions first, increase if all fail
5. **Combine with search** - Use lean_loogle/leansearch alongside tactic generation
6. **Document successes** - Note which tactics worked for future reference
7. **Stop daemon when done** - Run `./tactic_server.sh stop` at end of session
8. **Treat as inspiration** - Model may suggest outdated lemmas, but the approach is often right
