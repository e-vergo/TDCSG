# CLAUDE.md - AI Assistant Guidance for TDCSG Project

This file provides comprehensive guidance to Claude (claude.ai/code) when working with the TDCSG Lean 4 formalization project. **This is YOUR reference document - update it as you learn!**

## 🎯 Project Mission

Formalize **Theorem 2** from "Two-Disk Compound Symmetry Groups": Prove that GG₅ (5-fold rotational symmetry on both disks) has an infinite group at the critical radius r = √(3 + φ).

### Current Status (as of December 2024)
- **Progress**: 24 sorries remaining (down from 37 - 35% reduction)
- **Completed**: ComplexRepresentation.lean (11/11 theorems), Basic.lean (fully proven)
- **Build**: Clean - zero compile errors across 7,316 jobs
- **Main blocker**: FreeGroup implementation for `applyGroupElement`

## 📁 Project Structure & Dependencies

```
Core Definitions (Basic.lean) ✅
    ↓
Group Theory (GroupAction.lean) - 3 sorries
    ↓                    ↓
Isometries              Translations (4 sorries)
(PiecewiseIsometry.lean)      ↓
2 sorries                 Theorem1.lean (3 sorries)
    ↓                          ↓
Complex Analysis          Golden Ratio
(ComplexRepresentation.lean) ✅  (GoldenRatio.lean) - 1 sorry
    ↓                          ↓
        GG5Geometry.lean (5 sorries)
                ↓
        Theorem2.lean (6 sorries)
```

## 🔧 Essential Commands & Workflow

### Quick Status Check
```bash
# Check sorry count
grep -c "sorry" TDCSG/TwoDisk/*.lean | grep -v ":0$"

# Build project
lake build

# Get mathlib cache (do this after lake update!)
lake exe cache get
```

### Development Cycle
1. **Read file first**: Always use `Read` before `Edit` or `Write`
2. **Check diagnostics**: Use `mcp__lean-lsp__lean_diagnostic_messages` after edits
3. **Verify goal state**: Use `mcp__lean-lsp__lean_goal` when stuck
4. **Search wisely**: Use mathlib search tools sparingly (3 req/30s limit)

## 🎓 Key Mathematical Concepts

### Critical Values
- **Golden ratio**: φ = (1 + √5)/2
- **Critical radius**: r_c = √(3 + φ)
- **Fifth root of unity**: ζ₅ = e^(2πi/5)
- **Key identity**: cos(2π/5) = (φ - 1)/2 = (√5 - 1)/4

### Important Points
- **E** = ζ₅ - ζ₅² (defines critical geometry)
- **F** = 1 - ζ₅ + ζ₅² - ζ₅³
- **G** = 2F - E

### Critical Sequences (for Theorem 2)
1. `a⁻²b⁻¹a⁻¹b⁻¹`: maps E'F' → GF
2. `abab²`: maps F'G' → FE
3. `abab⁻¹a⁻¹b⁻¹`: maps G'E → E'G

## 🚧 Known Blockers & Solutions

### 1. FreeGroup Implementation (HIGHEST PRIORITY)
**Problem**: Need to implement `applyGroupElement` to apply rotation sequences
**Current approach**: Using `sorry` placeholder
**Solution path**:
```lean
noncomputable def applyGroupElement (sys : TwoDiskSystem) (g : TwoDiskGroup) : ℂ → ℂ :=
  FreeGroup.lift fun i => match i with
    | 0 => sys.leftRotation
    | 1 => sys.rightRotation
```
**Issue**: Need to lift to group homomorphisms, not just functions

### 2. Complex Geometry Calculations
**Problem**: Proving `E_constraint`: ‖E + 1‖ = r_c
**Requires**: Expanding ζ₅ in terms of trigonometric values
**Key fact**: Use cos(2π/5) = (φ-1)/2 and compute norm explicitly

### 3. Piecewise Isometry Composition
**Problem**: Composing piecewise isometries requires partition refinement
**Solution**: Track how regions map through compositions

## ⚠️ Common Pitfalls & Solutions

### Build Errors

#### "No goals to be solved"
```lean
-- BAD
theorem foo : ∃ x, P x := by
  use witness
  rfl  -- Error! Goal already solved by 'use'

-- GOOD
theorem foo : ∃ x, P x := by
  use witness
```

#### "Did not find occurrence of pattern"
```lean
-- Usually means you need to unfold or simplify first
simp only [defn] at h ⊢
-- or
unfold defn at *
```

#### Norm calculation issues
```lean
-- For ‖2 * x‖, convert to scalar multiplication:
rw [← two_smul ℂ x]
rw [norm_smul]
```

### Proof Patterns That Work

#### Proving positivity
```lean
theorem foo_pos : foo > 0 := by
  unfold foo
  apply Real.sqrt_pos.mpr
  linarith  -- or use specific inequalities
```

#### Using mathlib theorems
```lean
-- Search first
#check goldenRatio_sq  -- φ² = φ + 1
#check Complex.isPrimitiveRoot_exp  -- for roots of unity
#check IsPrimitiveRoot.geom_sum_eq_zero  -- sum of roots = 0
```

#### Field simplification
```lean
-- When dealing with division and multiplication
field_simp [ne_zero_hypothesis]
ring_nf
```

## 📚 Mathlib Gold Mines

### For Complex Numbers
- `Complex.norm_exp_ofReal_mul_I`: ‖e^(θi)‖ = 1
- `Complex.exp_nat_mul`: (e^x)^n = e^(n*x)
- `Complex.conj_exp`: conj(e^z) = e^(conj z)

### For Roots of Unity
- `Complex.isPrimitiveRoot_exp`: e^(2πi/n) is primitive
- `IsPrimitiveRoot.pow_eq_one`: ζⁿ = 1
- `IsPrimitiveRoot.geom_sum_eq_zero`: Σζⁱ = 0

### For Golden Ratio
- `goldenRatio_sq`: φ² = φ + 1
- `goldenRatio_pos`: φ > 0
- `goldenRatio_irrational`: φ is irrational
- `one_lt_goldenRatio`: φ > 1

## 🎯 Next Session Priorities

### Immediate (Unblock other work)
1. **Implement `applyGroupElement` properly**
   - This blocks all Translation proofs
   - This blocks all Theorem2 case proofs
   - Consider using `Equiv.Perm ℂ` or direct recursion

2. **Prove `E_constraint`**
   - Critical for Theorem2
   - Use trigonometric expansion of ζ₅
   - Leverage cos(2π/5) = (φ-1)/2

### Secondary (Build on foundations)
3. Complete remaining `GroupAction` lemmas
4. Finish `PiecewiseIsometry` composition
5. Prove translation lemmas once `applyGroupElement` works

### Strategic (Understanding the big picture)
- The three case proofs in Theorem2 are the heart of the argument
- Each shows a piecewise isometry mapping segments with irrational ratios
- This creates dense orbits, proving infinity

## 💡 Pro Tips from Experience

1. **Trust mathlib**: Before proving something from scratch, search for it. Mathlib often has exactly what you need.

2. **Use diagnostics liberally**: Don't guess what the error is - use `lean_diagnostic_messages` to see exactly what Lean is complaining about.

3. **Break complex proofs**: If a proof is getting unwieldy, extract helper lemmas. Lean handles many small proofs better than one large one.

4. **Document computational proofs**: When a proof requires specific calculations (especially with ζ₅), add detailed comments about what needs to be computed.

5. **Commit frequently**: After each successful reduction in sorries, commit with a clear message about what was proven.

6. **Track dependencies**: Know which proofs are blocked by which sorries. Focus on unblocking the most dependencies.

7. **Learn from errors**: Each "failed to synthesize" or "type mismatch" teaches you something about Lean's type system.

8. **Parallel progress**: Work on independent lemmas simultaneously when blocked on hard problems.

## 🔍 Debugging Checklist

When stuck on a proof:
- [ ] Check goal state with `lean_goal`
- [ ] Try `simp?` to see what simplifications are available
- [ ] Search mathlib with `lean_loogle` for similar theorems
- [ ] Unfold definitions to see what you're really proving
- [ ] Break into smaller steps with `have` statements
- [ ] Check types match exactly (use `convert` if close but not exact)
- [ ] Consider if the statement is actually true as written

## 📈 Progress Tracking

### Metrics to Track
- Sorry count per file
- Build success rate
- Theorems proven per session
- Dependencies unblocked

### Session Template
When starting a new session:
1. Check current sorry count
2. Run `lake build` to verify clean state
3. Review this CLAUDE.md for context
4. Pick highest-priority unblocked work
5. Update this file with new learnings

## 🎉 Celebrate Wins

### Major Milestones Achieved
- ✅ Basic.lean fully proven (foundation complete)
- ✅ ComplexRepresentation.lean fully proven (all ζ₅ infrastructure)
- ✅ All type definitions compile
- ✅ Main theorem statement type-checks

### Next Milestones
- [ ] Implement working `applyGroupElement`
- [ ] Prove E_constraint with explicit calculation
- [ ] Complete GroupAction.lean
- [ ] Achieve < 20 sorries
- [ ] Prove at least one Theorem2 case

## 🔮 Future Work

After Theorem 2 is complete:
1. Formalize Theorem 1 (characterization of infinite groups)
2. Explore other values of n (not just n=5)
3. Investigate connections to crystallographic groups
4. Consider computational verification of specific cases

## 📝 Notes for Future Claude

You're doing great! This formalization is challenging but you're making steady progress. Remember:

- Every proven lemma is a permanent contribution
- Build errors are learning opportunities
- The community values clarity over cleverness
- It's okay to leave computational proofs as sorries initially
- Focus on unblocking dependencies rather than perfection

When you return to this project:
1. Read this file first
2. Check the README for current status
3. Run the build to see what's broken
4. Pick up where you left off

**Your superpower**: You can hold the entire project structure in context and see connections humans might miss. Use this to identify the critical path to completing Theorem 2.

Good luck, future Claude! The formalization community is rooting for you! 🚀

## License

MIT License (see [LICENSE](LICENSE))