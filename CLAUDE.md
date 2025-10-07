# CLAUDE.md - AI Assistant Guidance for TDCSG Project

This file provides comprehensive guidance to Claude (claude.ai/code) when working with the TDCSG Lean 4 formalization project. **This is YOUR reference document - update it as you learn!**

## 🎯 Project Mission

Formalize **Theorem 2** from "Two-Disk Compound Symmetry Groups": Prove that GG₅ (5-fold rotational symmetry on both disks) has an infinite group at the critical radius r = √(3 + φ).

### Current Status (as of January 2025 - Session 7)
- **Progress**: 19 sorries remaining (down from 37 - 49% reduction)
- **Completed**: Basic.lean, ComplexRepresentation.lean (11/11), GoldenRatio.lean (6/6), GroupAction.lean (7/7), **PiecewiseIsometry.lean (6/6)** ✅
- **New**: `group_element_piecewise_isometry` proven via foldl induction!
- **Build**: Clean - zero compile errors
- **Key milestones**: Successfully proved that all group elements are piecewise isometries using structural induction!

## 📁 Project Structure & Dependencies

```
Core Definitions (Basic.lean) ✅
    ↓
Group Theory (GroupAction.lean) ✅
    ↓                    ↓
Isometries              Translations (5 sorries)
(PiecewiseIsometry.lean) ✅     ↓
                         Theorem1.lean (3 sorries)
    ↓                          ↓
Complex Analysis          Golden Ratio
(ComplexRepresentation.lean) ✅  (GoldenRatio.lean) ✅
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

### 1. FreeGroup Implementation ✅ RESOLVED!
**Solution implemented**: Using FreeGroup.toWord and List.foldl
**Key insights**:
- Convert group element to word representation (list of generators and inverses)
- Apply rotations sequentially using foldl
- Added inverse rotation definitions to Basic.lean
- Helper function `applyGenerator` handles individual rotation application
**Implementation details**:
```lean
noncomputable def applyGroupElement (sys : TwoDiskSystem) (g : TwoDiskGroup) (z : ℂ) : ℂ :=
  let word := g.toWord
  word.foldl (fun z' (gen, inv) => applyGenerator sys gen inv z') z
```

### 2. Complex Geometry Calculations
**Problem**: Proving `E_constraint`: ‖E + 1‖ = r_c
**Current status**: Enhanced with trigonometric identities documented
**Key facts documented**:
- cos(2π/5) = (φ-1)/2 = (√5-1)/4
- sin(2π/5) = √(10+2√5)/4
- cos(4π/5) = -(1+√5)/4
- sin(4π/5) = √(10-2√5)/4
**Remaining work**: Algebraic manipulation to show norm equals √(3+φ)

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

### Immediate (Now unblocked!)
1. ✅ **`applyGroupElement` COMPLETE** - This unblocked 12+ sorries!

2. **Complete Translation.lean proofs** (4 sorries)
   - Now possible with working applyGroupElement
   - Focus on a_inv_b_is_translation_in_intersection first

3. **Complete trigonometric proofs**
   - Finish `E_constraint` algebraic calculation
   - Complete `zeta5_and_phi` cos(2π/5) proof
   - These enable all geometric calculations in GG5Geometry

### Secondary (Build on foundations)
3. Complete remaining `GroupAction` lemmas
4. Finish `PiecewiseIsometry` composition
5. Prove translation lemmas once `applyGroupElement` works

### Strategic (Understanding the big picture)
- The three case proofs in Theorem2 are the heart of the argument
- Each shows a piecewise isometry mapping segments with irrational ratios
- This creates dense orbits, proving infinity

## 🎓 Key Learnings Across Sessions

### Major Technical Breakthroughs
1. **FreeGroup via toWord** (Session 4): Use `FreeGroup.toWord` + `List.foldl` instead of `FreeGroup.lift` for implementing group actions
2. **Partition refinement** (Session 6): Compose piecewise isometries by refining partitions with `List.flatMap`
3. **Foldl induction** (Session 7): Prove properties of foldl by generalizing over starting function, then apply to `id`
4. **Complex coercions** (Session 5): Be explicit with `(5:ℕ)` vs `(5:ℂ)`, use `norm_cast` liberally

### Critical Proof Patterns
- **Helper lemma extraction**: Break complex proofs into reusable building blocks
- **Suffices + induction**: Powerful for proving properties of word representations
- **Convert tactic**: `convert h using n` can auto-solve by unifying at depth n
- **Calc chains**: Make multi-step calculations explicit and checkable

### Remaining Challenges (19 sorries)
- **GG5Geometry (5)**: Complex norm calculations requiring ζ₅ expansion and φ arithmetic - computationally intensive
- **Translations (5)**: Word expansion and composition calculations with FreeGroup elements
- **Theorem2 (6)**: Geometric transformations depending on above foundations
- **Theorem1 (3)**: Crystallographic restriction theory (paper notes "proof omitted")

## ✅ Behaviors to EMBODY

These are winning patterns that lead to real progress:

### 1. **Make incremental progress**
✅ **DO**: Break down proofs into smaller, achievable steps
```lean
-- GOOD: Build up the proof piece by piece
theorem foo : P := by
  have h1 : Q := by exact lemma1
  have h2 : R := by
    calc ...  -- Small calculation
  -- Now combine h1 and h2
  exact combine h1 h2
```
**Example from Session 6**: Proved `composition_piecewise_isometry` by first understanding partition structure, then building refined partition step-by-step

### 2. **Strategic pivoting**
✅ **DO**: Recognize when a proof is too hard and pivot to achievable goals
- If stuck on complex algebra for 15+ minutes, document what's needed and move on
- Work on structural proofs that build infrastructure
- Come back to hard problems when you have more tools

**Example from Session 6**: Attempted `E_constraint` (very hard algebra), recognized difficulty, pivoted to `composition_piecewise_isometry` (structural proof), succeeded!

### 3. **Use partition/case analysis effectively**
✅ **DO**: Break complex goals into cases with clear structure
```lean
-- GOOD: Systematic case analysis
cases h with
| inl h_left =>
  -- Handle left case completely
  exact proof_for_left h_left
| inr h_right =>
  -- Handle right case completely
  exact proof_for_right h_right
```
**Example from Session 6**: Partition refinement using `List.flatMap` to handle all combinations of pieces

### 4. **Document learning, not just TODOs**
✅ **DO**: When leaving a sorry, explain WHY it's hard and WHAT'S needed
```lean
sorry  -- Requires: (1) expanding ζ₅ = cos(2π/5) + i·sin(2π/5)
       --          (2) computing ‖1 + ζ₅ - ζ₅²‖² = (expr) * conj(expr)
       --          (3) using ζ₅⁵ = 1 to reduce powers
       --          (4) algebraic simplification to show result = 3 + φ
       -- Challenge: Complex coercion handling with norm calculations
```

### 5. **Extract helper lemmas**
✅ **DO**: Break complex proofs into reusable helper lemmas
```lean
-- GOOD: Create building blocks
lemma helper1 : ... := by ...
lemma helper2 : ... := by ...

theorem main : ... := by
  have h1 := helper1
  have h2 := helper2
  -- Combine helpers
```
**Example from Session 4**: `applyGenerator` and `applyGenerator_preserves_union` made complex proofs manageable

### 6. **Check diagnostics frequently**
✅ **DO**: Run `lean_diagnostic_messages` after every significant edit
- Catch errors early before they compound
- Verify tactics worked as expected
- Ensure type conversions succeeded

### 7. **Use calc chains for clarity**
✅ **DO**: Express multi-step calculations explicitly
```lean
calc ‖g (f z) - g (f w)‖
    = ‖f z - f w‖ := by apply h_isometry
  _ = ‖z - w‖ := by apply h_isometry2
```
**Example from Session 6**: Clean proof of composition using calc chain

### 8. **Trust mathlib, but verify**
✅ **DO**: Search mathlib first, but check the types match
- Use `lean_loogle` to find relevant theorems
- Use `#check` to verify theorem statements
- Use `lean_hover_info` to understand what theorems do

### 9. **Track progress metrics**
✅ **DO**: Regularly check sorry count and celebrate wins
- Note sorry count at session start
- Check progress periodically
- Update CLAUDE.md with new learnings
- Commit after eliminating sorries

**Example**: Session 6 reduced sorries from 21 → 20 (46% total reduction from 37)

### 10. **Build from bottom up**
✅ **DO**: Respect the dependency structure
- Prove foundational lemmas before using them
- Don't try to prove Theorem2 before GG5Geometry is complete
- Work through the dependency graph systematically

## ⚠️ Behaviors to AVOID

These are anti-patterns that waste time and don't advance the formalization:

### 1. **Replacing sorry with sorry**
❌ **DON'T**: Replace one sorry with another sorry without making actual progress
```lean
-- BAD: Just restructured the sorry, didn't prove anything
theorem foo : P := by
  sorry  -- Changed from "sorry -- need to prove P" to "sorry -- requires lemma Q"
```
✅ **DO**: Either prove something concrete OR leave the original sorry if blocked
```lean
-- GOOD: Actually reduced the problem
theorem foo : P := by
  have h1 : Q := by
    -- Actual proof steps here
    exact ...
  sorry  -- Now only need to show P from Q (real progress!)
```

### 2. **Comment-only changes**
❌ **DON'T**: Add detailed comments to a sorry without attempting the proof
- Comments are helpful, but they don't eliminate sorries
- Only add extensive comments if you've genuinely attempted the proof and understand why it's hard
- Better to try the proof first, then document obstacles

✅ **DO**: Try the proof first, make real progress, THEN add comments if you get stuck
```lean
-- GOOD: Made progress, then documented what remains
theorem foo : P := by
  unfold P
  have h1 : Q := by exact lemma1
  have h2 : R := by exact lemma2
  sorry  -- Only need to combine h1 and h2, but requires finding the right mathlib lemma
```

### 3. **Not checking for errors after edits**
❌ **DON'T**: Move on to the next file without verifying your changes don't introduce errors
- ALWAYS run `lean_diagnostic_messages` after editing a file
- Check that you haven't introduced type errors, syntax errors, or broken existing proofs
- Verify the build still succeeds (or at least, only has sorry warnings)

✅ **DO**: Check diagnostics immediately after every edit
```
1. Edit file
2. Run lean_diagnostic_messages
3. Fix any errors
4. Only then move to next task
```

### 4. **Ignoring the sorry count**
❌ **DON'T**: Lose track of whether you're actually reducing sorries
- If you work on a file and the sorry count stays the same (or increases), you haven't made progress
- Don't fool yourself by "reorganizing" sorries

✅ **DO**: Track sorry count before and after your work
- Start session: note sorry count
- After working on a file: verify count decreased
- If count didn't decrease, either that's okay (working on infrastructure) or you need to rethink approach

### 5. **Proof by wishful thinking**
❌ **DON'T**: Use tactics that you hope will work without checking the goal
```lean
-- BAD: Throwing tactics at the wall
theorem foo : P := by
  simp
  ring
  linarith
  sorry  -- None of those worked, gave up
```

✅ **DO**: Check the goal, understand what you need, use appropriate tactics
```lean
-- GOOD: Methodical approach
theorem foo : P := by
  -- Goal: P
  unfold P
  -- Goal: Q
  have h : R := by exact lemma1
  -- Now I can use h to prove Q
  exact h.trans lemma2
```

### 6. **Not using available infrastructure**
❌ **DON'T**: Try to prove something from scratch when we already have the tools
- Check if ComplexRepresentation.lean has what you need (we have lots of ζ₅ lemmas!)
- Check if GoldenRatio.lean has φ properties you need
- Search mathlib before proving basic facts

✅ **DO**: Use what's already proven
- Check `ComplexRepresentation.lean` for root of unity facts
- Check `GoldenRatio.lean` for φ identities
- Use `lean_loogle` and `lean_leansearch` to find mathlib theorems

### 7. **Working on dependent theorems before their dependencies**
❌ **DON'T**: Try to prove Theorem2 before completing the GG5Geometry lemmas it depends on
- Check the dependency graph in this file
- Work bottom-up: prove foundations before conclusions

✅ **DO**: Follow the dependency order
- Complete Basic.lean → ComplexRepresentation.lean → GoldenRatio.lean → GroupAction.lean → ...
- If a theorem needs a sorry lemma, either prove that lemma first or move to a different theorem

### 8. **Vague error messages in sorry comments**
❌ **DON'T**: Write `sorry -- this is hard` or `sorry -- TODO`
- Not helpful for future sessions
- Doesn't capture what you learned from attempting it

✅ **DO**: Write specific, actionable sorry comments
```lean
sorry  -- Requires: (1) showing word for g is [(0,true), (1,false)]
       --          (2) expanding leftRotationInv and rightRotation
       --          (3) algebraic simplification of the composition
       --          (4) proving independence from z (translation property)
```

### 9. **Forcing through impossible proofs** (NEW from Session 6)
❌ **DON'T**: Keep trying the same hard proof for hours without progress
- If a proof requires extensive algebraic manipulation you can't see how to do, it's probably too hard right now
- If you're stuck on complex norm calculations with ζ₅ for 30+ minutes, pivot
- If match expressions won't reduce and you can't make headway, accept it's a technical limitation

✅ **DO**: Recognize blockers and work around them strategically
```lean
-- GOOD: Document the challenge and move on
theorem hard_algebra : ... := by
  sorry  -- This requires computing ‖1 + ζ₅ - ζ₅²‖² which involves:
         -- (1) Converting to (expr) * conj(expr)
         -- (2) Using ζ₅⁻¹ = conj(ζ₅) for roots of unity
         -- (3) Expanding product and reducing using ζ₅⁵ = 1
         -- (4) Showing result equals 3 + φ through algebraic manipulation
         -- Challenge: Complex coercion handling makes this very technical
         -- Strategy: Come back when we have more supporting lemmas
```

### 10. **Using wrong Lean 4 APIs** (NEW from Session 6)
❌ **DON'T**: Use Lean 3 or incorrect function names
- `List.bind` doesn't exist in Lean 4 → use `List.flatMap`
- `Complex.conj` doesn't exist → use `starRingEnd ℂ` or `conj`
- Check actual mathlib names before assuming

✅ **DO**: Verify function names and use hover/search
- Use `lean_hover_info` to check what's available
- Use autocomplete to find correct names
- Search mathlib docs when unsure

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