# START HERE - Quick Onboarding for AI Assistants

Welcome to the TDCSG (Two-Disk Compound Symmetry Groups) Lean 4 formalization project!

## 🎯 Your Mission

You are helping formalize **Theorem 2** from the paper "Two-Disk Compound Symmetry Groups" - proving that GG₅ (5-fold rotational symmetry on both disks) has an infinite group at the critical radius r = √(3 + φ).

## 📚 Essential Reading (Read in This Order)

Before doing **anything else**, read these four files to understand the project:

### 1. **[README.md](README.md)** - Project Overview
**Read this first** to understand:
- What the project is about
- Current progress (21 sorries remaining, 43% complete)
- File structure and organization
- Which theorems are proven vs. still need work
- Build instructions and dependencies

### 2. **[CLAUDE.md](CLAUDE.md)** - Your Comprehensive Guide
**This is your primary reference** - read it thoroughly:
- Current status and progress tracking
- Known blockers and their solutions
- Common pitfalls and how to avoid them
- Proof patterns that work
- Mathlib gold mines (useful theorems)
- **BFS-Prover section** - How to use the AI tactic generator
- Pro tips from previous sessions
- Debugging checklist

### 3. **[two-disk_compound_symmetry_groups.tex](two-disk_compound_symmetry_groups.tex)** - The Mathematics
**Read this to understand the math** being formalized:
- The actual theorem statements
- Mathematical definitions and concepts
- The proof strategy for Theorem 2
- Why the golden ratio and fifth roots of unity are important
- The geometric intuition behind the proofs

### 4. **[BFS_PROVER_MCP_GUIDE.md](BFS_PROVER_MCP_GUIDE.md)** - AI Tactic Generator (YOUR SUPERPOWER!)
**Read this to learn your most powerful tool**:
- Native MCP integration (fully operational!)
- Simple 3-step workflow: get goal → generate tactics → test
- No daemon management needed (auto-starts)
- Real testing results: ~30-40% success rate
- Performance: ~6 seconds per 10 tactics
- Temperature guidelines for different proof types

## ⚡ Quick Start After Reading

Once you've read the above files:

1. **Check current status:**
   ```bash
   grep -c "sorry" TDCSG/**/*.lean | grep -v ":0$"
   lake build
   ```

2. **Verify BFS-Prover MCP is ready:**
   ```bash
   claude mcp list  # Should show bfs_prover: ✓ Connected
   ```

   Or check model status directly:
   ```
   mcp__bfs_prover__model_info()
   ```

3. **Review CLAUDE.md** for:
   - Current session priorities (Session 11 section)
   - Known blockers and solutions
   - BFS-Prover workflow
   - Behaviors to AVOID

4. **Pick a task** based on:
   - Dependency order (see CLAUDE.md project structure)
   - What's unblocked (check sorry comments)
   - User's specific request

## 🚨 Critical Rules

**DO:**
- ✅ Read the files above before starting work
- ✅ Use BFS-Prover MCP tools for tactic suggestions (auto-starts, ~6s per query!)
- ✅ Test ALL BFS-Prover suggestions with `multi_attempt`
- ✅ Check diagnostics after every edit
- ✅ Track sorry count (should decrease!)
- ✅ Update CLAUDE.md with new learnings
- ✅ Commit frequently with clear messages

**DON'T:**
- ❌ Replace sorry with sorry (see "Behaviors to AVOID" in CLAUDE.md)
- ❌ Add comments without attempting the proof
- ❌ Work on dependent theorems before their dependencies
- ❌ Ignore the sorry count
- ❌ Spend >2 minutes on a sorry without trying BFS-Prover
- ❌ Skip reading these files!

## 📊 Current Status Snapshot

As of Session 10 (January 2025):
- **27 sorries remaining** (down from 36, 9 eliminated! 57% total reduction from start)
- **6 files complete**: Basic.lean, Complex.lean, Constants.lean, FreeGroup.lean, GG5Properties.lean
- **Near-complete files**: GroupAction.lean (90%), IsometrySimple.lean (83%)
- **Build status**: ✅ CLEAN - zero compile errors
- **BFS-Prover MCP**: ✅ FULLY OPERATIONAL - Native integration, auto-starts, ~6s per query
- **Session 10 achievements**: Broke through <30 sorries barrier, discovered piecewise isometry pattern!

**NEW in January 2025:**
- 🎉 **BFS-Prover MCP fully integrated** - No daemon management needed!
- 🚀 **Tested and verified** - 30-40% success rate across proof types
- 📚 **Complete documentation** - BFS_PROVER_MCP_GUIDE.md with real examples

## 🎓 Key Concepts to Understand

After reading the files, you should understand:
- **Golden ratio (φ)**: (1 + √5)/2, satisfies φ² = φ + 1
- **Fifth root of unity (ζ₅)**: e^(2πi/5), satisfies ζ₅⁵ = 1
- **Critical radius (r_c)**: √(3 + φ), the special radius where GG₅ is infinite
- **Points E, F, G**: Special geometric points defined using ζ₅
- **Piecewise isometries**: Functions that preserve distances on parts of their domain
- **Translation sequences**: Rotation sequences that act like translations

## 🔧 Available Tools

You have access to:

### AI-Powered Tactic Generation (USE THIS!)
- **`mcp__bfs_prover__suggest_tactics`** - Generate 10 Lean tactics from proof state (~6s)
- **`mcp__bfs_prover__model_info`** - Check model status (26.89 GB, Metal accelerated)
- **`mcp__bfs_prover__reload_model`** - Reload model if needed

### Lean LSP Integration
- **`mcp__lean-lsp__lean_goal`** - Get proof state at cursor position
- **`mcp__lean-lsp__lean_diagnostic_messages`** - Check for errors/warnings
- **`mcp__lean-lsp__lean_multi_attempt`** - Test multiple tactics automatically
- **`mcp__lean-lsp__lean_loogle`** - Search by type signature
- **`mcp__lean-lsp__lean_leansearch`** - Natural language theorem search
- **`mcp__lean-lsp__lean_hover_info`** - Get documentation for terms

### Standard Tools
- **File tools**: Read, Edit, Write, Grep, Glob, Bash
- **Git tools**: For commits and tracking changes

## 📝 First Steps Checklist

- [ ] Read README.md (project overview)
- [ ] Read CLAUDE.md (your comprehensive guide)
- [ ] Read two-disk_compound_symmetry_groups.tex (the math)
- [ ] Read BFS_PROVER_MCP_GUIDE.md (AI tactic generator)
- [ ] Check current sorry count: `grep -c "sorry" TDCSG/**/*.lean | grep -v ":0$"`
- [ ] Verify BFS-Prover MCP: `claude mcp list` or `mcp__bfs_prover__model_info()`
- [ ] Review "Session 11 Priorities" in CLAUDE.md
- [ ] Ask user what they want to work on

## 💡 Pro Tips

1. **CLAUDE.md is your bible** - Updated throughout the project with learnings, blockers, and working patterns
2. **BFS-Prover is your superpower** - Use it for EVERY sorry, takes only 6 seconds!
3. **Test in batches** - Generate 10 tactics, test all with `multi_attempt`, pick the winner
4. **Track your progress** - Sorry count should DECREASE each session

## 🎉 You're Ready!

After reading these files, you'll have:
- ✅ Understanding of the mathematical goal
- ✅ Knowledge of what's been proven
- ✅ Awareness of what's blocked and why
- ✅ AI-powered tactic generation (BFS-Prover MCP)
- ✅ Proven patterns and strategies
- ✅ List of pitfalls to avoid

**Your workflow for each sorry:**
1. `mcp__lean-lsp__lean_goal(file, line)` → Get proof state
2. `mcp__bfs_prover__suggest_tactics(goal, 10, 0.7)` → Generate tactics
3. `mcp__lean-lsp__lean_multi_attempt(file, line, tactics)` → Test all
4. Apply winner with `Edit` tool

Now go eliminate some sorries! 🚀

---

**Remember**: Every proven lemma is permanent progress. Build errors are learning opportunities. The formalization community values clarity over cleverness. You've got this! 💪
