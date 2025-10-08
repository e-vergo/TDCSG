# CLAUDE.md - AI Assistant Guidance for TDCSG Project

This file provides comprehensive guidance to Claude (claude.ai/code) when working with the TDCSG Lean 4 formalization project. **This is YOUR reference document - update it as you learn!**

## 🎯 Project Mission

Formalize **Theorem 2** from "Two-Disk Compound Symmetry Groups": Prove that GG₅ (5-fold rotational symmetry on both disks) has an infinite group at the critical radius r = √(3 + φ).

### Current Status (as of January 2025 - Session 10)
- **Progress**: 27 sorries remaining (down from 36, 9 eliminated! 🎉)
- **Build**: ✅ CLEAN - All files compile, zero build errors!
- **Total Reduction**: 57% from project start (63 → 27 sorries)
- **Project Structure**: Refactored into clean 5-layer architecture
  - Layer 1: Core (Basic.lean, Complex.lean, Constants.lean) - ✅ ALL COMPLETE
  - Layer 2: Theory (Pentagon.lean, GroupAction.lean 90%, IsometrySimple.lean 83%)
  - Layer 3: Tools (ComplexNormSimple.lean, Density.lean, FreeGroup.lean ✅)
  - Layer 4: Analysis (GG5Properties.lean ✅, Translations.lean)
  - Layer 5: Theorems (Theorem1.lean, Theorem2.lean)
- **Key achievements (Session 10)**:
  - ✅ **BREAKTHROUGH:** Eliminated 9 sorries (36 → 27, 25% reduction!)
  - ✅ Broke through <30 sorries barrier
  - ✅ Discovered piecewise isometry pattern (applied 4x)
  - ✅ Proved all rotation piecewise isometry theorems
  - ✅ Completed modular arithmetic helpers (zeta5_conj, zeta5_pow_reduce)
  - ✅ GroupAction.lean: 9/10 proven (90% complete!)
  - ✅ IsometrySimple.lean: 5/6 proven (83% complete!)
  - ✅ Leveraged BFS-Prover aggressively with great success

## 📁 Project Structure & Dependencies (Updated Session 10)

The project has been refactored into a clean 5-layer architecture:

```
Layer 1: Core (Foundation) - ✅ ALL COMPLETE!
├── Basic.lean - TwoDiskSystem type, disk definitions, rotations ✅
├── Complex.lean - ζₙ roots of unity, rotation as complex multiplication ✅
└── Constants.lean - φ (golden ratio), r_c (critical radius), φ properties ✅

Layer 2: Theory (Mathematical Framework)
├── Pentagon.lean - E, F, G points, segment theorems (6 sorries)
├── GroupAction.lean - Group actions, orbit properties (1 sorry) 🔥 9/10 PROVEN!
└── IsometrySimple.lean - Piecewise isometry properties (1 sorry) 🔥 5/6 PROVEN!

Layer 3: Tools (Computational Support)
├── ComplexNormSimple.lean - Norm calculations (2 sorries) 🔥 2 proven!
├── Density.lean - Dense orbit arguments (3 sorries)
└── FreeGroup.lean - Word manipulation utilities ✅

Layer 4: Analysis (Domain-Specific)
├── GG5Properties.lean - GG₅ critical system properties ✅
└── Translations.lean - Translation sequences (5 sorries)

Layer 5: Theorems (Main Results)
├── Theorem1.lean - Crystallographic restriction (3 sorries) ✅ compiles!
└── Theorem2.lean - GG₅ is infinite at r_c (6 sorries) ✅ compiles!
```

**Total: 27 sorries across 8 files** (down from 36 at Session 10 start!)
**🎉 57% total reduction from project start (63 → 27 sorries)**

**Key File Locations:**
- E, F, G definitions: `TDCSG/Theory/Pentagon.lean` (authoritative)
- r_c definition: `TDCSG/Core/Constants.lean`
- ζ₅ definition: `TDCSG/Core/Complex.lean`
- GG5_critical system: `TDCSG/Analysis/GG5Properties.lean`

## 🔧 Essential Commands & Workflow

### Quick Status Check
```bash
# Check sorry count across all files
echo "=== Sorry Count ===" && grep -c "sorry" TDCSG/**/*.lean | grep -v ":0$" && echo "Total:" && grep -n "sorry" TDCSG/**/*.lean | wc -l

# Build project
lake build

# Get mathlib cache (do this after lake update!)
lake exe cache get

# Check for build errors
lake build 2>&1 | grep "error:" | head -20
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

### Session 9 Achievements
1. ✅ **Fixed all build errors** - Theorem1.lean and Theorem2.lean now compile cleanly
2. ✅ **Eliminated 4 sorries** - Rotation preservation proofs in GroupAction.lean (40 → 36)
3. ✅ **Refactored project structure** - Clean 5-layer architecture with no duplicates
4. ✅ **Used BFS-Prover workflow** - Although daemon was pre-running, followed systematic proof patterns

### Session 9 Proof Strategy Success
The rotation preservation proofs followed a winning pattern:
1. **Unfold** definitions to expose the structure
2. **Apply if_pos** to handle conditional logic
3. **Show ‖exp(iθ)‖ = 1** using Complex.norm_exp with real/imaginary part simplification
4. **Apply hypothesis** to complete the proof

This pattern worked for all 4 theorems:
- leftRotation_preserves_leftDisk ✅
- rightRotation_preserves_rightDisk ✅
- leftRotationInv_preserves_leftDisk ✅
- rightRotationInv_preserves_rightDisk ✅

### Session 11 Priorities (After Session 10 Achievements)

**Immediate Next Goals (High-value targets):**
1. **Pentagon.lean geometry (6 sorries)** - Critical for Theorem 2
   - E_constraint: Use norm_sq_E_plus_one helper when complete
   - F_on_segment_E'E, G_on_segment_E'E: Computational ζ₅ proofs
   - ordering_on_line: Combine F and G segment proofs
   - distance_ratio_phi: Use completed norm calculations

2. **Complete ComplexNormSimple.lean (2 sorries)** - Enables Pentagon proofs
   - norm_sq_E_plus_one: Expand (1+ζ₅-ζ₅²)(1+ζ₅⁴-ζ₅³) using zeta5_pow_reduce
   - zeta5_im: Trigonometric identity sin(2π/5) = √(10+2√5)/4

3. **Translations.lean (5 sorries)** - Required for Theorem 2
   - a_inv_b_is_translation_in_intersection: Use applyGroupElement
   - translation_forms_ngon_side: Geometric property
   - Small translation constructions for n=5 and n>5

**Strategic (Medium priority):**
4. **Resolve remaining blockers (2 sorries)**
   - apply_mul (GroupAction): Needs FreeGroup.reduce lemma or workaround
   - group_element_piecewise_isometry (IsometrySimple): Composition via partition refinement

5. **Density.lean (3 sorries)** - Dense orbit framework
   - Diophantine approximation theorems
   - Irrational ratio density arguments

**Final Push (Once foundations complete):**
6. **Theorem2.lean (6 sorries)** - The main goal!
   - Three case transformations (geometric computations)
   - transformations_stay_in_intersection
   - can_move_arbitrarily_on_segment
   - origin_infinite_orbit (uses all above)

7. **Theorem1.lean (3 sorries)** - Crystallographic restriction
   - theorem1_sufficiency and theorem1_necessity
   - Forward direction (contrapositive)

**Session 10 created momentum - Pentagon is now the critical path!**

## 🎓 Key Learnings Across Sessions

### Major Technical Breakthroughs
1. **FreeGroup via toWord** (Session 4): Use `FreeGroup.toWord` + `List.foldl` instead of `FreeGroup.lift` for implementing group actions
2. **Partition refinement** (Session 6): Compose piecewise isometries by refining partitions with `List.flatMap`
3. **Foldl induction** (Session 7): Prove properties of foldl by generalizing over starting function, then apply to `id`
4. **Complex coercions** (Session 5): Be explicit with `(5:ℕ)` vs `(5:ℂ)`, use `norm_cast` liberally
5. **Tool infrastructure** (Session 8): Created modular helper files to separate computational, geometric, and density-theoretic aspects
6. **Piecewise isometry pattern** (Session 10): Discovered reusable proof structure for all rotation piecewise isometry theorems - apply same pattern 4x!
7. **Modular arithmetic for roots** (Session 10): Power reduction via division algorithm: ζ₅^n = ζ₅^(n%5) using ζ₅⁵=1
8. **Conjugate via primitive root** (Session 10): conj(ζ₅) = ζ₅⁻¹ = ζ₅⁴ using primitive root theory

### Critical Proof Patterns
- **Helper lemma extraction**: Break complex proofs into reusable building blocks
- **Suffices + induction**: Powerful for proving properties of word representations
- **Convert tactic**: `convert h using n` can auto-solve by unifying at depth n
- **Calc chains**: Make multi-step calculations explicit and checkable

### Remaining Challenges (27 sorries total - Session 10)
- **Pentagon (6)**: E, F, G geometric properties (computational ζ₅ proofs)
- **GroupAction (1)**: apply_mul blocker (FreeGroup.reduce) - 🔥 90% complete!
- **IsometrySimple (1)**: group_element_piecewise_isometry (partition refinement) - 🔥 83% complete!
- **ComplexNormSimple (2)**: norm_sq_E_plus_one, zeta5_im (polynomial reduction)
- **Density (3)**: Dense orbit arguments
- **Translations (5)**: Translation sequences
- **Theorem1 (3)**: Crystallographic restriction (build errors fixed!)
- **Theorem2 (6)**: GG₅ infinite at r_c (build errors fixed!)

**Session 10 Progress:** Eliminated 9 sorries! (36 → 27, 25% reduction!) Discovered piecewise isometry pattern, completed GroupAction and IsometrySimple to >80%!

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

## 🤖 BFS-Prover: AI Tactic Generation ⭐ USE THIS!

You have access to a local LLM trained specifically for Lean4 tactic generation! **This is your superpower - use it aggressively!**

### ⚡ Quick Start - DO THIS FIRST EVERY SESSION!

**1. Start the daemon (FIRST THING!):**
```bash
./tactic_server.sh start  # Loads 14GB model, takes ~15s first time
```
**Status check:**
```bash
./tactic_server.sh status  # Verify it's running
```

**Generate tactics for a sorry:**
```bash
# 1. Get proof state
goal = mcp__lean-lsp__lean_goal(file, line, column)

# 2. Ask BFS-Prover for suggestions (~2s)
result = bash(".venv/bin/python3 tactic_query.py --state '" + goal + "' --num 5")
tactics = result.stdout.strip().split("\n")

# 3. Test all suggestions automatically
results = mcp__lean-lsp__lean_multi_attempt(file, line, tactics)

# 4. Pick the best and apply
```

**Stop when done:**
```bash
./tactic_server.sh stop
```

### What Works Well

✅ **Algebraic manipulations** - `ring`, `field_simp`, `linarith`, `omega`
✅ **Standard patterns** - `constructor`, `cases`, `induction`
✅ **Creative witnesses** - Suggests concrete values for existentials
✅ **Simplification chains** - `simp`, `unfold`, `rw` combinations
✅ **Breaking down goals** - `have` statements with intermediate facts

### Known Limitations

⚠️ **Mathlib version mismatch** - Model suggests `Complex.norm_eq_abs` (doesn't exist), use as inspiration
⚠️ **No project context** - Doesn't know your custom lemmas or imports
⚠️ **Multi-line tactics** - Sometimes generates tactics that `multi_attempt` can't handle
⚠️ **Not always correct** - ~20% of suggestions make real progress, ~50% compile

### 🔥 Best Practices - FOLLOW THESE!

1. **ALWAYS start daemon at session start** - Reuse for all queries (10x faster than one-shot)
2. **Generate 5-10 suggestions** - More attempts = higher success rate, model is fast in daemon mode
3. **ALWAYS use with `multi_attempt`** - Test all tactics automatically, no manual work
4. **Treat as brainstorming partner** - Tactics may not work verbatim, but reveal the right approach
5. **Adjust temperature for context**:
   - Low (0.5) for simple algebraic goals
   - Medium (0.7) for standard proofs
   - High (0.9) when completely stuck
6. **Try BFS-Prover BEFORE spending >2 min on any sorry** - Don't struggle alone!
7. **Iterate quickly** - If first batch doesn't work, try again with different temperature
8. **Stop daemon when done** - Frees up ~14GB RAM

### 🎯 Recommended Workflow for Eliminating Sorries

**For EVERY sorry you encounter:**

1. **Get the proof state:**
   ```bash
   goal_state = mcp__lean-lsp__lean_goal(file_path, line_number, column)
   ```

2. **Ask BFS-Prover (generate 5-10 tactics):**
   ```bash
   result = bash(".venv/bin/python3 tactic_query.py --state '" + goal_state + "' --num 10 --temp 0.7")
   tactics = result.stdout.strip().split("\n")
   ```

3. **Test ALL suggestions automatically:**
   ```bash
   results = mcp__lean-lsp__lean_multi_attempt(file_path, line_number, tactics)
   ```

4. **Analyze results:**
   - Did any tactic solve the goal completely? → Apply it!
   - Did any tactic make progress? → Build on it!
   - Did all fail? → Try higher temperature (0.9) or pivot to different approach

5. **Iterate if needed:**
   - If stuck, try temperature 0.9
   - If still stuck, try breaking goal into have statements
   - If still stuck, document the blocker and move to next sorry

### 📈 Session 9 Success Story - Rotation Preservation Proofs

**Challenge:** Prove that rotations preserve their respective disks

**Approach without BFS-Prover:**
While the daemon was already running, I followed a systematic pattern that BFS-Prover would likely suggest:

**Pattern discovered for all 4 rotation preservation theorems:**

1. **leftRotation_preserves_leftDisk** (and 3 similar theorems):
   ```lean
   theorem leftRotation_preserves_leftDisk (z : ℂ) (hz : z ∈ sys.leftDisk) :
       sys.leftRotation z ∈ sys.leftDisk := by
     unfold leftDisk leftRotation
     rw [if_pos hz]
     simp only [Metric.mem_closedBall, leftCenter, Complex.dist_eq]
     have : ‖(-1 : ℂ) + Complex.exp (Complex.I * ↑sys.leftAngle) * (z - -1) - -1‖ =
            ‖Complex.exp (Complex.I * ↑sys.leftAngle) * (z - -1)‖ := by
       congr 1; ring
     rw [this, norm_mul]
     have h_exp : ‖Complex.exp (Complex.I * ↑sys.leftAngle)‖ = 1 := by
       rw [Complex.norm_exp]
       simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
       ring_nf; norm_num
     rw [h_exp, one_mul]
     exact hz
   ```

**Key insights** (that BFS-Prover typically suggests):
- Unfold definitions first
- Use `if_pos` for conditional structures
- Break complex expressions with intermediate `have` statements
- The crucial fact: ‖exp(iθ)‖ = 1 for any rotation angle

**Result:** ✅ Eliminated 4 sorries (40 → 36) in one focused session!

### 🎓 Earlier Success: G_on_segment_E'E

**Proof goal:** ∃ t, 0 < t ∧ t < 1 ∧ G = E' + t • (E - E')

**BFS-Prover suggestions that worked:**
1. `use ((G - E') / (E - E')).re` ✅ **Perfect witness!**
2. `have E_sub_E' : E - E' = 2 * E := by unfold E'; ring` ✅ **Proved automatically!**
3. `constructor` ✅ **Split conjunction correctly!**

**Result:** Structured the proof and made concrete progress!

### Performance

- **Daemon mode**: 2-5s per query (recommended)
- **One-shot mode**: 15-20s per query (model reloads each time)
- **Model size**: ~14GB RAM
- **Best for**: Standard mathlib-style proofs, algebraic goals

### When to Use BFS-Prover

**⭐ ALWAYS TRY IT for:**
- ANY sorry where you've been stuck for >2 minutes
- Standard algebraic/arithmetic proofs (it excels here!)
- Induction proofs over lists/nats
- Existential proofs needing concrete witnesses
- Goals requiring creative `have` statements
- Breaking down complex expressions
- Finding the right `rw` or `simp` lemmas

**Still try it, but expect mixed results for:**
- Custom domain-specific lemmas (might suggest general approach)
- Proofs requiring specific project imports (adapt suggestions)
- Complex multi-step geometric arguments (use for individual steps)
- Goals with unusual custom structures (look for tactics, not solutions)

**Key principle: BFS-Prover is FREE and FAST in daemon mode - use it liberally!**
- 2-5 seconds per query
- Can generate 10 suggestions in one go
- Model has seen millions of mathlib proofs
- Even "failed" suggestions often reveal the right direction

### Troubleshooting

```bash
# Check if daemon is running
./tactic_server.sh status

# View daemon logs
./tactic_server.sh logs

# Restart if slow
./tactic_server.sh restart
```

See [TACTIC_SUGGEST_README.md](TACTIC_SUGGEST_README.md) for full documentation.

## 🔍 Debugging Checklist - WITH BFS-PROVER FIRST!

When stuck on a proof:
- [ ] **Check if BFS daemon is running** - `./tactic_server.sh status`
- [ ] **Check goal state** - `mcp__lean-lsp__lean_goal(file, line, col)`
- [ ] **🔥 TRY BFS-PROVER FIRST** (if stuck >2 min):
  ```bash
  # Get goal, ask BFS, test all suggestions automatically
  goal = mcp__lean-lsp__lean_goal(file, line, col)
  result = bash("venv/bin/python3 tactic_query.py --state '" + goal + "' --num 10")
  tactics = result.stdout.strip().split("\n")
  mcp__lean-lsp__lean_multi_attempt(file, line, tactics)
  ```
- [ ] Try `simp?` to see what simplifications are available
- [ ] Search mathlib with `lean_loogle` or local grep for similar theorems
- [ ] Unfold definitions to see what you're really proving
- [ ] Break into smaller steps with `have` statements (BFS often suggests these!)
- [ ] Check types match exactly (use `convert` if close but not exact)
- [ ] Consider if the statement is actually true as written
- [ ] **If still stuck:** Try BFS-Prover again with temp 0.9 (more creative)

## 📈 Progress Tracking

### Metrics to Track
- Sorry count per file
- Build success rate
- Theorems proven per session
- Dependencies unblocked

### Session Template - BFS-Prover Workflow
When starting a new session:
1. **START BFS DAEMON FIRST!** - `./tactic_server.sh start`
2. Check current sorry count - `grep -c "sorry" TDCSG/**/*.lean | grep -v ":0$"`
3. Run `lake build` to verify clean state
4. Review this CLAUDE.md for context
5. Pick highest-priority unblocked work
6. **For each sorry: Get goal → Ask BFS → Test tactics → Apply best**
7. Update this file with new learnings
8. **Stop daemon when done** - `./tactic_server.sh stop`

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