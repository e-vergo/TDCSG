# CLAUDE.md - AI Assistant Guidance for TDCSG Project

This file provides comprehensive guidance to Claude (claude.ai/code) when working with the TDCSG Lean 4 formalization project. **This is YOUR reference document - update it as you learn!**

## 🎯 Project Mission

Formalize **Theorem 2** from "Two-Disk Compound Symmetry Groups": Prove that GG₅ (5-fold rotational symmetry on both disks) has an infinite group at the critical radius r = √(3 + φ).

### Current Status (as of January 2025 - Session 5)
- **Progress**: 21 sorries remaining (down from 37 - 43% reduction)
- **Completed**: Basic.lean, ComplexRepresentation.lean (11/11), **GoldenRatio.lean (6/6)**, **GroupAction.lean (7/7)**
- **Build**: Clean - zero compile errors
- **Key milestones**: `zeta5_and_phi` proven!, `points_stay_in_union` and `intersection_points_can_stay_bounded` proven!

## 📁 Project Structure & Dependencies

```
Core Definitions (Basic.lean) ✅
    ↓
Group Theory (GroupAction.lean) ✅
    ↓                    ↓
Isometries              Translations (4 sorries)
(PiecewiseIsometry.lean)      ↓
2 sorries                 Theorem1.lean (3 sorries)
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

## 🆕 Session 5 Learnings

### Key Achievements
1. **GoldenRatio.lean COMPLETE**: Successfully completed the `zeta5_and_phi` proof connecting ζ₅ = cos(2π/5) + i·sin(2π/5) where cos(2π/5) = (φ-1)/2. This was a major milestone requiring careful handling of complex coercions and the double angle formula.

2. **GroupAction.lean COMPLETE**: Finished all remaining theorems including:
   - `points_stay_in_union`: Points moved by group elements stay in disk union
   - `intersection_points_can_stay_bounded`: Points in intersection remain in union
   - Used induction on word representations and the `suffices` pattern effectively

3. **Enhanced documentation across all files**: Added detailed proof strategies and mathematical insights to all remaining sorries, making future work much clearer.

4. **Eliminated 4 sorries**: Reduced from 25 to 21 (16% reduction this session, 43% total from start).

### Technical Insights
- **Coercion handling**: When working with `/5`, need to be explicit about `(5:ℕ)` vs `(5:ℂ)` and use `norm_cast` liberally
- **Double angle formula**: `Real.cos_two_mul` combined with `Real.cos_pi_div_five` gives cos(2π/5) = (φ-1)/2
- **Induction pattern**: The `suffices` tactic followed by induction on lists is powerful for proving properties of `foldl`
- **Type conversions**: `Complex.exp_mul_I` requires complex arguments, then use `norm_cast` to convert between Real and Complex

### Lessons Learned
- Trust the existing infrastructure: `zeta5_and_phi` was achievable using mathlib's existing trigonometric theorems
- Build incrementally: Proving smaller helper facts first (like the coercion equality) makes the main proof clearer
- Documentation pays dividends: Detailed comments about what remains to be proven help maintain momentum across sessions

## 🆕 Session 4 Learnings

### Key Achievements
1. **FreeGroup implementation breakthrough**: Successfully implemented `applyGroupElement` using FreeGroup.toWord instead of struggling with FreeGroup.lift. This simpler approach works perfectly for our needs.

2. **Inverse rotations added**: Extended Basic.lean with `leftRotationInv` and `rightRotationInv` definitions, completing the group action structure.

3. **Helper lemmas strategy**: Created `applyGenerator` and `applyGenerator_preserves_union` as intermediate steps, making proofs more manageable.

4. **Translation theorems structured**: Set up the framework for Translation.lean proofs, now that applyGroupElement is working.

### Technical Insights
- FreeGroup.toWord provides a list representation that's easier to work with than the abstract FreeGroup structure
- List.foldl is perfect for sequential application of rotations
- The pattern `word.foldl (fun z' (gen, inv) => applyGenerator sys gen inv z') z` elegantly handles composition

### Lessons Learned
- Sometimes the simpler approach (toWord + foldl) is better than the theoretically elegant one (FreeGroup.lift)
- Breaking complex functions into helpers (applyGenerator) makes both implementation and proofs easier
- Documentation improvements in earlier sessions paid off by guiding this session's implementation

## 🆕 Session 3 Learnings

### Key Insights
1. **FreeGroup.lift complexity**: The natural approach of using `FreeGroup.lift` fails because `ℂ → ℂ` doesn't form a group under composition. Need to think in terms of automorphisms or bijections.

2. **Trigonometric identities for ζ₅**: The relationship between fifth roots of unity and the golden ratio is deep. Key identity: cos(2π/5) = (φ-1)/2 connects regular pentagons to φ.

3. **Documentation as progress**: Even when unable to complete a proof, documenting the specification and intended behavior helps future sessions understand the goal clearly.

4. **Sorry tracking matters**: Small increases in sorry count (24→25) can happen when improving documentation or restructuring, but the overall trend should be downward.

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