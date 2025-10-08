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

### 4. **[TACTIC_SUGGEST_README.md](TACTIC_SUGGEST_README.md)** - BFS-Prover Tool
**Read this to learn your superpower**:
- How to use the local LLM for tactic generation
- Daemon mode (10x faster than one-shot)
- Integration with Lean LSP tools
- What works well and what doesn't
- Performance metrics and best practices

## ⚡ Quick Start After Reading

Once you've read the above files:

1. **Check current status:**
   ```bash
   grep -c "sorry" TDCSG/TwoDisk/*.lean | grep -v ":0$"
   lake build
   ```

2. **Start BFS-Prover daemon** (if working on proofs):
   ```bash
   ./tactic_server.sh start
   ```

3. **Review CLAUDE.md** for:
   - Current session priorities
   - Known blockers
   - Behaviors to AVOID

4. **Pick a task** based on:
   - Dependency order (see CLAUDE.md)
   - What's unblocked
   - User's specific request

## 🚨 Critical Rules

**DO:**
- ✅ Read the four files above before starting work
- ✅ Use BFS-Prover for tactic suggestions (daemon mode!)
- ✅ Check diagnostics after every edit
- ✅ Track sorry count (should decrease!)
- ✅ Update CLAUDE.md with new learnings
- ✅ Commit frequently with clear messages

**DON'T:**
- ❌ Replace sorry with sorry (see "Behaviors to AVOID" in CLAUDE.md)
- ❌ Add comments without attempting the proof
- ❌ Work on dependent theorems before their dependencies
- ❌ Ignore the sorry count
- ❌ Skip reading these files!

## 📊 Current Status Snapshot

As of Session 10 (January 2025):
- **27 sorries remaining** (down from 36, 9 eliminated! 57% total reduction from start)
- **6 files complete**: Basic.lean, Complex.lean, Constants.lean, FreeGroup.lean, GG5Properties.lean
- **Near-complete files**: GroupAction.lean (90%), IsometrySimple.lean (83%)
- **Build status**: ✅ CLEAN - zero compile errors
- **BFS-Prover**: Daemon system ready, tested, and working
- **Session 10 achievements**: Broke through <30 sorries barrier, discovered piecewise isometry pattern!

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
- **Lean LSP MCP tools**: `lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, `lean_loogle`, `lean_leansearch`, etc.
- **BFS-Prover tactic daemon**: Local LLM for generating Lean tactics
- **Standard file tools**: Read, Edit, Write, Grep, Glob, Bash
- **Git tools**: For commits and tracking changes

## 📝 First Steps Checklist

- [ ] Read README.md (project overview)
- [ ] Read CLAUDE.md (your comprehensive guide)
- [ ] Read two-disk_compound_symmetry_groups.tex (the math)
- [ ] Read TACTIC_SUGGEST_README.md (BFS-Prover tool)
- [ ] Check current sorry count
- [ ] Review "Next Session Priorities" in CLAUDE.md
- [ ] Start BFS-Prover daemon if working on proofs
- [ ] Ask user what they want to work on

## 💡 Pro Tip

The most important file is **CLAUDE.md** - it's been updated throughout the project with learnings, solutions to blockers, and patterns that work. Treat it as your primary reference and update it as you learn new things.

## 🎉 You're Ready!

After reading these files, you'll have:
- Understanding of the mathematical goal
- Knowledge of what's been proven
- Awareness of what's blocked and why
- Tools to generate tactics automatically
- Patterns and strategies that work
- Pitfalls to avoid

Now go formalize some mathematics! 🚀

---

**Remember**: Every proven lemma is permanent progress. Build errors are learning opportunities. The formalization community values clarity over cleverness. You've got this! 💪
