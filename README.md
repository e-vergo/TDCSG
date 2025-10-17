# TDCSG - Piecewise Isometries Formalization

## Current Status

**Remaining Sorries:** 32 across 5 files
**Build Status:** ✅ All files compile with zero errors

### Files by Status

**Complete (0 sorries):**
- [TDCSG/Basic.lean](TDCSG/Basic.lean) - Core definitions for `PiecewiseIsometry` structure
- [TDCSG/Properties.lean](TDCSG/Properties.lean) - Basic properties and lemmas
- [TDCSG/MeasurePreserving.lean](TDCSG/MeasurePreserving.lean) - Measure-theoretic properties (all unprovable theorems removed with counter-examples documented)

**In Progress:**
- [TDCSG/Composition.lean](TDCSG/Composition.lean) - **2 sorries** - Category structure (comp_assoc, identity laws complete; measurability proven under BorelSpace)
- [TDCSG/Ergodic.lean](TDCSG/Ergodic.lean) - **4 sorries** - All research-level (Masur-Veech, Keane, Hopf decomposition)
- [TDCSG/IntervalExchange.lean](TDCSG/IntervalExchange.lean) - **17 sorries** - IET definitions and properties (intervals_cover forward direction complete)
- [TDCSG/Examples.lean](TDCSG/Examples.lean) - **8 sorries** - Concrete constructions (partition_cover proven, metric mismatch documented)
- [TDCSG/Finite.lean](TDCSG/Finite.lean) - **1 sorry** - Finite partition specializations

---

## CRITICAL TOOL: Lean Diagnostic Extraction

**Location:** [check_lean.sh](check_lean.sh)

**Purpose:** Extract complete, unclipped error messages from Lean builds with maximum token efficiency.

### Usage Patterns

**Errors-only mode (MANDATORY for proof testing):**
```bash
./check_lean.sh --errors-only TDCSG/YourFile.lean
```
- Returns `✓ No errors` if proof compiles (exit code 0)
- Shows complete error with full context if proof fails (exit code 1)
- **99.4% token reduction** vs raw `lake build` output
- Filters out all warnings and build noise

**All diagnostics mode (for code quality):**
```bash
./check_lean.sh TDCSG/YourFile.lean
```
- Shows errors AND warnings
- Use when investigating linter warnings or deprecations

### Integration with Agent Workflow

**MANDATORY iteration loop:**
1. Edit proof
2. Run `./check_lean.sh --errors-only TDCSG/File.lean`
3. Interpret:
   - `✓ No errors` → proof works, proceed
   - Error output → read full diagnostic, fix, retry

**Why this matters:**
- Previous agents used `head`/`tail` which clipped messages, missing critical errors
- This tool provides 100% of diagnostics with zero clipping
- Token efficiency enables many more agent iterations per context window

**Technical details:** [CHECK_LEAN_TOOL.md](CHECK_LEAN_TOOL.md)

---

## Critical Blockers

### Composition.lean:757 - `iterate_finite_discontinuities`

**Challenge:** Prove that iterating a piecewise isometry with finite discontinuities preserves finiteness.

**Goal State:**
```lean
f : PiecewiseIsometry α
n : ℕ
hf : Set.Finite (discontinuities f)
⊢ Set.Finite (discontinuities (f^[n]))
```

**Attempted Approaches:**
- Induction on n (base case trivial: `f^[0] = id` has empty discontinuities)
- Inductive step requires: `discontinuities(f^[n+1]) = discontinuities(f ∘ f^[n])`
- Composition discontinuity formula: `disc(f ∘ g) ⊆ disc(g) ∪ f⁻¹(disc(f))`
- **Problem:** Without injectivity, `f⁻¹(finite set)` can be infinite (e.g., constant maps)

**Missing Pieces:**
- Either add hypothesis: `Injective f.toFun`
- Or add bounded-fiber property: `∀ y, Set.Finite (f.toFun ⁻¹' {y})`
- Or change statement to weaker property

**Potential Path:** Add injectivity hypothesis (justified for most piecewise isometry applications where each piece is an isometry, hence injective).

**In-file documentation:** Lines 719-757

---

### Finite.lean:445 - `comp_measure_preserving`

**Challenge:** Prove composition of finite piecewise isometries preserves measure.

**Goal State:**
```lean
f g : FinitePiecewiseIsometry α
hf : IsMeasurePreserving f.toFun μ
hg : IsMeasurePreserving g.toFun μ
⊢ IsMeasurePreserving (f.comp g).toFun μ
```

**Attempted Approaches:**
- Use measure preservation of composition: if both preserve measure, composition preserves measure
- Standard theorem for measurable functions

**Missing Pieces:**
- Lemma `IsMeasurePreserving.comp` may not exist in Mathlib for piecewise functions
- May need to prove: `μ((f ∘ g)⁻¹(s)) = μ(g⁻¹(f⁻¹(s))) = μ(f⁻¹(s)) = μ(s)`
- Requires measurability of both f and g (proven for BorelSpace in Composition.lean:206)

**Potential Path:** Search Mathlib for `IsMeasurePreserving.comp` or `MeasureTheory.measure_preimage_comp`. If not found, construct direct proof using:
```lean
calc μ((f.comp g).toFun ⁻¹' s)
    = μ(g.toFun ⁻¹' (f.toFun ⁻¹' s)) := rfl
    _ = μ(f.toFun ⁻¹' s) := hg _
    _ = μ(s) := hf _
```

**In-file documentation:** Lines 422-445

---

### IntervalExchange.lean:244 - Fin sum inequality

**Challenge:** Prove partial sum less than or equal to total sum for Fin types.

**Goal State:**
```lean
iet : IntervalExchangeTransformation n
i j : Fin n
hij : i < j
⊢ ∑ k : Fin i.val, lengths k + lengths i ≤ ∑ k : Fin j.val, lengths k
```

**Attempted Approaches:**
- Use `Fin.sum_univ_castSucc` to convert LHS to sum over `Fin (i.val + 1)`
- Apply `Finset.sum_le_sum_of_subset_of_nonneg` with subset inclusion `i.val + 1 ≤ j.val`
- **Issue:** Careful type coercions needed between `Fin i.val`, `Fin j.val`, and underlying `ℕ` values

**Missing Pieces:**
- Lemma relating `Finset.range (i.val + 1) ⊆ Finset.range j.val` when `i < j`
- Or use `Fin.cast` to embed `Fin (i.val + 1)` into `Fin j.val`
- All lengths are positive (from `IntervalExchangeTransformation` definition)

**Potential Path:**
```lean
have h_le : i.val.succ ≤ j.val := Nat.succ_le_of_lt (Fin.val_fin_lt.mpr hij)
calc ∑ k : Fin i.val, lengths k + lengths i
  _ = ∑ k : Fin i.val.succ, lengths (Fin.cast h_le_n k) := Fin.sum_univ_castSucc
  _ ≤ ∑ k : Fin j.val, lengths k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · -- Prove Finset.range i.val.succ ⊆ Finset.range j.val using h_le
    · -- All terms nonnegative
```

**In-file documentation:** Lines 230-244

---

### IntervalExchange.lean:208 - `intervals_cover` (reverse direction)

**Challenge:** Prove every point in `[0, total_length)` belongs to some interval.

**Goal State:**
```lean
x : ℝ
hx : x ∈ Icc 0 (∑ i : Fin n, iet.lengths i)
⊢ ∃ i : Fin n, x ∈ iet.interval i
```

**Attempted Approaches:**
- Constructively find the interval containing x
- Use `Finset.sum_lt_sum` to show partial sums partition the domain
- **Issue:** Requires decidability or classical choice to pick the right interval

**Missing Pieces:**
- Helper function to find interval index: `findInterval : ℝ → Fin n`
- Prove it works: `x ∈ [domainLeft i, domainRight i) → x ∈ interval i`
- Use strong induction or recursion on `Fin n`

**Potential Path:**
```lean
-- Find largest i such that domainLeft i ≤ x
use Fin.find (fun i => domainLeft (i + 1) > x)
-- Or use classical.choose with existence proof
have ⟨i, hi⟩ := exists_interval_containing x hx
exact ⟨i, hi⟩
```

**Mathematical content:** The intervals `[domainLeft i, domainRight i)` partition `[0, total_length)` by construction. Need to make this computationally effective.

**In-file documentation:** Lines 200-208

---

### IntervalExchange.lean:302 & 312 - IET Conversions

**Challenge:** Implement `toPiecewiseIsometry` and `toFinitePiecewiseIsometry`.

**Goal:** Convert `IntervalExchangeTransformation` to `PiecewiseIsometry ℝ`.

**Structure Required:**
```lean
noncomputable def toPiecewiseIsometry : PiecewiseIsometry ℝ where
  partition := Set.range iet.interval  -- Countable: Fin n is finite
  countable := Set.countable_range _
  measurable := fun s hs => by
    -- Each interval [domainLeft i, domainRight i) is measurable (Icc measurable)
    obtain ⟨i, rfl⟩ := hs
    exact measurableSet_Icc
  cover := iet.intervals_cover  -- Proven (forward direction) at line 170
  nonempty := fun s hs => by
    -- Each interval is nonempty (lengths i > 0)
    obtain ⟨i, rfl⟩ := hs
    use iet.domainLeft i
    exact ⟨domainLeft_in_interval i⟩
  disjoint := iet.intervals_disjoint  -- Need to prove (line 247)
  isometry := fun s hs => by
    -- On interval i, map is translation by (rangeLeft i - domainLeft i)
    -- Translations are isometries
    obtain ⟨i, rfl⟩ := hs
    exact isometry_translation _
  continuousOn := fun s hs => by
    -- Translations are continuous
    exact continuous_translation.continuousOn
```

**Missing Pieces:**
- `intervals_disjoint` (line 247) - requires `domainRight_le_domainLeft_of_lt` (blocked on line 244)
- Explicit formula for the map on each interval (currently undefined)
- Type class instances for `MeasureSpace ℝ` (Mathlib has this, may need explicit import)

**Impact:** Unblocks 5 sorries in Examples.lean (lines 190, 199, 206, 1037, 1043)

**Potential Path:**
1. First complete lines 208, 244, 247 (coverage, sum inequality, disjointness)
2. Define the map explicitly: `toFun x := rangeLeft i + (x - domainLeft i)` where `i = findInterval x`
3. Prove each piece is an isometry (translation preserves distance)
4. Assemble into `PiecewiseIsometry` structure

---

### Examples.lean:346, 357 - `double_rotation` (DESIGN FLAW)

**Challenge:** Original construction uses ℝ × ℝ with sup metric, but rotations preserve L2 metric.

**Root Cause:** Type `ℝ × ℝ` has instance `Prod.instDist` using sup metric:
```
dist (x₁, y₁) (x₂, y₂) = max(|x₁ - x₂|, |y₁ - y₂|)
```

Rotation matrices preserve Euclidean (L2) distance:
```
dist (x₁, y₁) (x₂, y₂) = √((x₁ - x₂)² + (y₁ - y₂)²)
```

These are incompatible except for axis-aligned rotations.

**Resolution:** Line 346 documented as IMPOSSIBLE. Correct version created:

**Correct Construction:** `double_rotation_euclidean` (lines 359-520)
- Type: `PiecewiseIsometry EuclideanPlane` where `EuclideanPlane := PiLp 2 (Fin 2 → ℝ)`
- Uses L2 metric at type level
- All structural proofs complete (partition_countable, measurable, cover, nonempty, disjoint)
- Two remaining sorries (lines 485, 512) with detailed proof sketches

**Proof sketch for remaining sorries:**
```lean
-- Line 485: Right half-disk isometry
calc dist (rotate_euclidean θ x) (rotate_euclidean θ y)
  _ = ‖(rotate_euclidean θ x).1 - (rotate_euclidean θ y).1‖ := PiLp.dist_comm_apply
  _ = ‖rotation_matrix θ (x.1 - y.1)‖ := by ring_nf
  _ = ‖x.1 - y.1‖ := by
    -- Rotation matrices preserve L2 norm
    -- Proof: ‖R v‖² = ⟨R v, R v⟩ = ⟨v, Rᵀ R v⟩ = ⟨v, v⟩ = ‖v‖²
    -- Use: Real.cos_sq_add_sin_sq, Matrix.transpose_mul for rotation matrices
  _ = dist x y := PiLp.dist_comm_apply.symm
```

**Required lemmas:**
- `PiLp.dist_comm_apply` - definition of distance in PiLp
- `Matrix.rotation_preserves_norm` - may need to prove or search Mathlib
- `Real.cos_sq_add_sin_sq` - identity cos²θ + sin²θ = 1

**In-file documentation:** Lines 329-357 (impossibility), lines 359-520 (correct version)

---

### Examples.lean:190, 199, 206, 1037, 1043 - IET Examples

**Blocker:** All depend on `IntervalExchangeTransformation.toPiecewiseIsometry` (line 302 in IntervalExchange.lean)

**Status:** Cannot proceed until IET conversion functions implemented.

**Action:** Complete IntervalExchange.lean first (see blockers above), then return to these examples.

---

### Ergodic.lean - All 4 sorries (RESEARCH-LEVEL)

**Status:** All confirmed to require mathematical machinery not in Mathlib as of 2025-01.

#### Line 302: `ergodic_iff_irreducible`
**Requires:** Hopf decomposition theorem (conservative + dissipative parts)
**Mathlib has:** `Mathlib.Dynamics.Ergodic.Conservative` (basic conservative dynamics)
**Missing:** Full Hopf decomposition with irreducibility characterization
**Literature:** Katok & Hasselblatt, "Introduction to the Modern Theory of Dynamical Systems"

#### Line 373: `uniquely_ergodic_of_irrational_data`
**Requires:** Masur-Veech Theorem (1982), Rauzy-Veech induction, Teichmüller flow
**Mathlib has:** Basic ergodic theory foundations
**Missing:** Entire theory of Teichmüller dynamics and IET renormalization
**Literature:** Masur (1982) "Interval Exchange Transformations and Measured Foliations", Veech (1982)

#### Line 492: `minimal_implies_uniquely_ergodic`
**Requires:** Keane's Theorem (1975), full Birkhoff ergodic theorem with decomposition
**Mathlib has:** `Ergodic.iff_mem_extremePoints` (partial decomposition)
**Missing:** Full ergodic decomposition theorem (convex hull of ergodic measures)
**Literature:** Keane (1975) "Interval Exchange Transformations"

#### Line 559: `ergodic_of_minimal`
**Requires:** Measure support theory, inner/outer regularity, Baire category arguments
**Mathlib has:** Basic topology and measure theory
**Missing:** Systematic theory of `Measure.support` on metric spaces with regularity
**Literature:** Walters, "An Introduction to Ergodic Theory", Theorem 6.11

**Recommendation:** Document these as research-level gaps. Future work: contribute to Mathlib or wait for community to formalize ergodic theory infrastructure.

---

## Proven Strategies

### Pattern: Extensionality via field equality
**Approach:** Create `ext_fields` lemmas that require proving all fields equal, use proof irrelevance for `Prop`-valued dependent fields.
```lean
theorem ext_fields (f g : PiecewiseIsometry α)
    (h_part : f.partition = g.partition)
    (h_fun : ∀ s ∈ f.partition, ∀ x ∈ s, f.toFun x = g.toFun x) :
    f = g
```
**Examples:** Composition.lean:191 (`ext_partition_toFun`), used in comp_assoc, comp_id proofs

### Pattern: Composition associativity via bidirectional set membership
**Approach:** Prove partition equality using `Set.ext` with `⟨→, ←⟩` pattern matching, then use `simp` for function equality.
```lean
apply ext_partition_toFun
· ext s
  simp only [comp_partition, Set.mem_image]
  constructor
  · intro ⟨t, ht, rfl⟩
    -- Forward direction
  · intro ⟨u, hu, rfl⟩
    -- Reverse direction
· intro s hs x hx
  simp [comp_toFun]
  -- Show function composition is definitionally equal
```
**Example:** Composition.lean:267 (`comp_assoc`)

### Pattern: Identity via refinement simplification
**Approach:** Show that refining with `univ` (or intersecting with preimage of `univ`) collapses to original partition.
```lean
-- s ∩ f⁻¹(univ) = s ∩ univ = s
simp only [Set.preimage_univ, Set.inter_univ]
```
**Examples:** Composition.lean:335 (`comp_id_left`), Composition.lean:371 (`comp_id_right`)

### Pattern: Frontier/boundary discontinuity proofs
**Approach:** Use frontier calculation lemmas to show boundary contained in candidate discontinuity set.
```lean
calc frontier piece
  _ = frontier (Iio x ×ˢ univ) ⊓ frontier (univ ×ˢ Iio y) := frontier_prod_eq
  _ = {x} ×ˢ univ ∪ univ ×ˢ {y} := by rw [frontier_Iio, frontier_univ, ...]
  _ ⊆ candidate_discontinuities := by ...
```
**Required lemmas:** `frontier_prod_eq`, `frontier_Iio`, `closure_Iio'`, `frontier_univ`
**Example:** Examples.lean:439 (`square_billiard_boundary_discontinuity`)

### Pattern: Countability via finite/range
**Approach:** Use `Set.countable_range` for finite index types, or `Set.Countable.image` for countable constructions.
```lean
countable_partition : Set.Countable partition := by
  have : partition = Set.range (fun i : Fin n => interval i) := rfl
  exact Set.countable_range _
```
**Required lemmas:** `Set.countable_range`, `Fintype.card_fin`, `Set.Countable.image`
**Example:** IntervalExchange.lean implicit in definition, Examples.lean:double_rotation_euclidean

### Pattern: Borel measurability via continuous restriction
**Approach:** For piecewise continuous functions on measurable sets, use `continuousOn_iff_continuous_restrict` and `MeasurableEmbedding.subtype_coe`.
```lean
theorem piecewiseIsometry_measurable [BorelSpace α] (f : PiecewiseIsometry α) :
    Measurable f.toFun := by
  apply measurable_of_isOpen
  intro U hU
  have : f⁻¹(U) = ⋃ s ∈ partition, (f⁻¹(U) ∩ s) := by ext; simp [cover]
  rw [this]
  apply MeasurableSet.iUnion
  intro s
  by_cases hs : s ∈ partition
  · -- f is continuous on s, use continuousOn_measurableSet_preimage
    exact continuousOn_measurableSet_preimage (continuousOn s) (measurable s hs) hU
  · simp [hs]
```
**Required:** `BorelSpace α` type class (stronger than `OpensMeasurableSpace α`)
**Required lemmas:** `continuousOn_iff_continuous_restrict`, `MeasurableEmbedding.subtype_coe`, `measurable_of_isOpen`
**Example:** Composition.lean:169-206 (new proof, complete)

---

## Key Mathematical Insights

1. **Metric type-level consistency:** Isometries must preserve the metric defined at the type level. Product types `α × β` use sup metric by default; for Euclidean geometry, use `PiLp 2 (Fin n → ℝ)`.

2. **Measurability requires BorelSpace:** While `OpensMeasurableSpace` suffices for some results, proving measurability of piecewise continuous functions requires `BorelSpace` to ensure `Continuous → Measurable` via `MeasurableEmbedding.subtype_coe`.

3. **Composition discontinuities grow without injectivity:** Formula `disc(f ∘ g) ⊆ disc(g) ∪ f⁻¹(disc(f))` means preimages of discontinuities matter. Without injectivity, preimages can be infinite even for finite discontinuity sets.

4. **Fin sum inequalities need careful type coercion:** When proving `∑_{i<n} a_i ≤ ∑_{i<m} a_i` for Fin types, use `Fin.sum_univ_castSucc` to convert between index types, then `Finset.sum_le_sum_of_subset_of_nonneg` with explicit subset proof.

5. **IET intervals partition by construction:** The intervals `[domainLeft i, domainRight i)` for an `IntervalExchangeTransformation` automatically partition `[0, total_length)` due to the definition of `domainLeft` and `domainRight` as cumulative sums. The proof challenge is making this effective/computational.

6. **Extensionality via field equality avoids axioms:** Instead of declaring equality of structures via axiom `ext`, prove equality by showing all fields equal. For `Prop`-valued fields (like proof obligations), use proof irrelevance after fixing non-`Prop` fields.

---

## Essential Resources

### Mathlib Files - Core Definitions

**Isometry and Metric Spaces:**
- `.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
  Key lemmas: `Isometry.comp`, `Isometry.continuous`, `Isometry.injective`

**Measurability and Borel Spaces:**
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
  Key: `BorelSpace` type class, `MeasurableEmbedding.subtype_coe`, `measurable_of_isOpen`

**Product Topology and Frontiers:**
- `.lake/packages/mathlib/Mathlib/Topology/Constructions.lean`
  Key lemmas: `frontier_prod_eq`, `frontier_Iio`, `closure_Iio'`

**Lp Norms and Euclidean Space:**
- `.lake/packages/mathlib/Mathlib/Analysis/NormedSpace/PiLp.lean`
  Key: `PiLp p (ι → α)` type, `PiLp.dist_comm_apply`, `WithLp.equiv` for conversions

**Ergodic Theory:**
- `.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Ergodic.lean`
  Current state: basic definitions, `Ergodic.iff_mem_extremePoints` (partial decomposition)
- `.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Conservative.lean`
  Poincaré recurrence, conservative maps (incomplete Hopf decomposition)

### Mathlib Files - Useful Lemmas

**Set Operations:**
- `Set.ext` - prove set equality via membership
- `Set.sUnion_eq_univ_iff` - union equals univ iff covering property
- `Set.PairwiseDisjoint` - definition and basic lemmas
- `Set.countable_range` - range of function from countable type is countable

**Fin Arithmetic:**
- `Fin.sum_univ_castSucc` - relate sum over `Fin n` to sum over `Fin (n+1)`
- `Fin.val_fin_lt` - ordering on Fin values
- `Finset.sum_le_sum_of_subset_of_nonneg` - monotonicity of sums over subsets

**Continuity and Measurability:**
- `continuousOn_iff_continuous_restrict` - continuous on set ↔ restriction is continuous
- `ContinuousOn.mono` - continuity on larger set → continuity on subset
- `MeasurableSet.iUnion` - countable union of measurable sets is measurable

**Critical Lemmas Discovered:**

**Composition.lean:169 - `continuousOn_measurableSet_preimage`**
```lean
theorem continuousOn_measurableSet_preimage [BorelSpace α] {f : α → α} {s U : Set α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) (hU : IsOpen U) :
    MeasurableSet (f ⁻¹' U ∩ s)
```
Proof strategy: Use measurable embedding `Subtype.val : s → α` and continuous restriction `s.restrict f`.

---

## Next Steps for Successor Agent

### Immediate Actions (High Priority)

1. **IntervalExchange.lean:244 - Complete Fin sum inequality**
   - Location: Line 244 in `domainRight_le_domainLeft_of_lt`
   - Strategy: Apply `Finset.sum_le_sum_of_subset_of_nonneg` after converting indices with `Fin.cast`
   - Impact: Unblocks `intervals_disjoint` (line 247) → enables `toPiecewiseIsometry` (line 302)
   - Estimated difficulty: Medium (requires careful Fin type juggling)

2. **IntervalExchange.lean:208 - Complete `intervals_cover` reverse direction**
   - Location: Line 208, prove `∀ x ∈ [0, total), ∃ i, x ∈ interval i`
   - Strategy: Use `Fin.find` or induction to construct witness interval
   - Impact: Required for `toPiecewiseIsometry.cover` field
   - Estimated difficulty: Medium-High (constructive proof with dependent types)

3. **IntervalExchange.lean:302, 312 - Implement IET conversions**
   - Blocked on: Lines 208, 244, 247 above
   - Once unblocked: Fill in structure fields using proven lemmas
   - Impact: Unblocks 5 Examples.lean sorries (lines 190, 199, 206, 1037, 1043)
   - Estimated difficulty: Low (mostly bookkeeping once prerequisites done)

### Research Priorities

1. **Search Mathlib for measure preservation composition:**
   - Query: `IsMeasurePreserving.comp` or `MeasureTheory.measure_preimage_comp`
   - Relevance: Needed for Finite.lean:445
   - If not found: Construct direct proof via calc chain

2. **Search Mathlib for rotation matrix norm preservation:**
   - Query: `Matrix.orthogonal_preserves_norm` or `rotation_matrix` + `Isometry`
   - Relevance: Needed for Examples.lean:485, 512 (double_rotation_euclidean isometry proofs)
   - If not found: May need to prove from first principles using cos²θ + sin²θ = 1

3. **Investigate stronger hypotheses for iterate_finite_discontinuities:**
   - Mathematical question: What minimal assumptions ensure `disc(f^n)` finite when `disc(f)` finite?
   - Literature search: Dynamical systems texts on piecewise isometries
   - Relevance: Composition.lean:757

### Strategic Approach

**Phase 1: Complete IntervalExchange.lean infrastructure** (sorries at lines 208, 244, 247, 302, 312)
- Order: 244 → 247 → 208 → 302 → 312
- Rationale: Line 244 unblocks 247, both needed for 302; line 208 also needed for 302
- Use `check_lean.sh --errors-only` after every edit
- Expected timeline: Can complete in single agent session

**Phase 2: Unblock Examples.lean IET examples** (sorries at lines 190, 199, 206, 1037, 1043)
- Once Phase 1 complete, these become straightforward applications
- Use newly implemented `toPiecewiseIsometry` conversion
- Expected timeline: Quick (mostly applying conversion function)

**Phase 3: Complete Examples.lean double_rotation_euclidean** (sorries at lines 485, 512)
- Detailed proof sketches already in file (lines 485-520)
- Requires lemmas about rotation matrices and PiLp norms
- Search Mathlib first, prove from scratch if needed
- Expected timeline: Medium (depends on Mathlib support for rotation matrices)

**Phase 4: Address measure preservation composition** (Finite.lean:445)
- After Phases 1-3, this is the highest-value remaining sorry
- Search Mathlib, construct direct proof if needed
- Expected timeline: Low-Medium (standard measure theory)

**Phase 5: Resolve Composition.lean:757 or document limitation**
- Research whether statement is provable without additional hypotheses
- If not: add hypothesis (injectivity or bounded-fiber) with justification
- If yes: find the trick (may require mathematical literature search)
- Expected timeline: High (research-level)

**De-prioritize:** Ergodic.lean (4 sorries) - all research-level, require major Mathlib contributions

---

## Technical Notes

### Type Class Requirements

**BorelSpace vs OpensMeasurableSpace:**
- `OpensMeasurableSpace α`: Open sets are measurable (weaker)
- `BorelSpace α`: Measurable sets are Borel σ-algebra generated by open sets (stronger)
- **Impact:** Proving `Measurable f` for piecewise continuous `f` requires `BorelSpace` to ensure `MeasurableEmbedding.subtype_coe` works correctly
- **Usage:** Composition.lean:206 theorem `piecewiseIsometry_measurable` requires `[BorelSpace α]`

**MeasureSpace instances:**
- ℝ has instance `Real.measureSpace` (Lebesgue measure)
- Product spaces `α × β` have instance `Prod.measureSpace` (product measure)
- `PiLp` types have appropriate measure space instances from base type
- **Issue:** Sometimes need explicit imports or instance declarations in `variable` blocks

### Import Requirements

**Critical imports for this project:**
```lean
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Topology.Constructions
```

**For IntervalExchange work:**
```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
```

**For measure preservation proofs:**
```lean
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.Prod.Basic
```

### Build Configuration

**Current status:** All 8 files compile with zero errors (verified via `check_lean.sh --errors-only`)

**Build command:** `lake build`
**Cache:** Mathlib cache downloaded via `lake update` (7,364 files)
**Total jobs:** ~2284 compilation units
**Clean build time:** ~5-10 minutes (with cache)

**Warnings (non-blocking):**
- Some files have linter warnings about unused `simp` arguments (cosmetic)
- Some files have deprecation warnings (use new lemma names when editing nearby code)

### Tool Usage - check_lean.sh

**When to use errors-only mode:**
- Testing if a proof compiles after edits (THE critical use case)
- Iterating on sorry elimination
- Verifying file status before moving to next task

**When to use all-diagnostics mode:**
- Investigating linter warnings
- Code quality checks
- Understanding deprecation warnings

**Exit code semantics:**
- 0 → success, can proceed
- 1 → has diagnostics, read output and fix
- 2 → usage error, check command syntax

**Token efficiency:**
- Errors-only mode: 99.4% reduction vs raw build output
- All-diagnostics mode: ~44% reduction vs raw build output
- Comparison: Old approach (raw `lake build`) output for Examples.lean = 6,086 chars; errors-only = 35 chars ("✓ No errors")

---

## In-File Documentation Protocol

All files follow standardized documentation format for failed proof attempts:

```lean
/- PROOF ATTEMPTS:
   Attempt 1 [date]: [strategy description]
   - Issue: [why it failed]
   - Lesson: [insight gained]

   Attempt 2 [date]: [different strategy]
   - Issue: [why it failed]
   - Lesson: [insight gained]

   Current status: [blocking issue or next direction to try]
-/
sorry
```

**Purpose:** Prevent successor agents from repeating failed approaches. Read these comments before attempting any sorry.

**Examples:**
- IntervalExchange.lean:208 - documents two failed attempts at constructive interval finding
- IntervalExchange.lean:244 - documents partial progress on sum inequality
- Composition.lean:757 - documents counter-example (constant map) showing need for stronger hypotheses
- Examples.lean:346 - documents why proof is impossible (metric mismatch)

---

## Remaining Sorry Inventory

### Composition.lean (2 sorries)
- Line 206: `piecewiseIsometry_measurable` - **COMPLETE** (proven under BorelSpace)
- Line 757: `iterate_finite_discontinuities` - Needs injectivity or bounded-fiber hypothesis

### Ergodic.lean (4 sorries - research-level)
- Line 302: `ergodic_iff_irreducible` - Requires Hopf decomposition theorem
- Line 373: `uniquely_ergodic_of_irrational_data` - Requires Masur-Veech Theorem (1982)
- Line 492: `minimal_implies_uniquely_ergodic` - Requires Keane's Theorem (1975)
- Line 559: `ergodic_of_minimal` - Requires Measure.support theory on metric spaces

### IntervalExchange.lean (17 sorries)
- Line 208: `intervals_cover` (reverse direction) - Find interval containing given point
- Line 244: `domainRight_le_domainLeft_of_lt` - Fin sum inequality (HIGH PRIORITY)
- Line 247: `intervals_disjoint` - Blocked on line 244
- Line 302: `toPiecewiseIsometry` - Blocked on lines 208, 244, 247
- Line 312: `toFinitePiecewiseIsometry` - Blocked on line 302
- Lines 317, 325, 330, 356, 361, 371, 375, 380, 400, 413, 418, 422: Various IET properties (lower priority)

### Examples.lean (8 sorries)
- Line 190: `simple_two_IET` - Blocked on IntervalExchange.lean:302
- Line 199: `simple_two_IET_preservation` - Blocked on IntervalExchange.lean:302
- Line 206: `simple_two_IET_ergodic` - Blocked on IntervalExchange.lean:302
- Line 346: `double_rotation.isometry_on_pieces` - **DOCUMENTED AS IMPOSSIBLE** (metric mismatch)
- Line 357: `double_rotation.double_rotation_discontinuity` - Blocked on impossible line 346
- Line 485: `double_rotation_euclidean` right half isometry - Detailed proof sketch provided
- Line 512: `double_rotation_euclidean` left half isometry - Detailed proof sketch provided
- Line 1037, 1043: Iterated IET examples - Blocked on IntervalExchange.lean:302

### Finite.lean (1 sorry)
- Line 445: `comp_measure_preserving` - Need `IsMeasurePreserving.comp` or direct proof

**Total:** 32 sorries remaining

**Breakdown:**
- 4 research-level (Ergodic.lean) - beyond current Mathlib scope
- ~15 blocked on IntervalExchange.lean infrastructure (lines 208, 244, 247, 302)
- ~8 addressable with current Mathlib (Finite.lean:445, Examples.lean:485/512, Composition.lean:757)
- 2 documented as impossible/flawed (Examples.lean:346, 357)

**Completion Status:** 32/~65 sorries remaining → ~51% complete (estimated original count ~65 based on project scope)

---

## References

### Mathlib Documentation
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/) - Search for lemmas and type classes
- [Loogle](https://loogle.lean-lang.org/) - Search by type signature
- [Moogle](https://www.moogle.ai/) - Natural language search for Mathlib

### Literature (for research-level sorries)

**Interval Exchange Transformations:**
- Keane (1975) "Interval Exchange Transformations" - Math. Z. 141
- Masur (1982) "Interval Exchange Transformations and Measured Foliations" - Ann. of Math.
- Veech (1982) "Gauss Measures for Transformations on the Space of Interval Exchange Maps" - Ann. of Math.

**Ergodic Theory:**
- Katok & Hasselblatt - "Introduction to the Modern Theory of Dynamical Systems" (Cambridge, 1995)
- Walters - "An Introduction to Ergodic Theory" (Springer GTM, 1982)
- Viana & Oliveira - "Foundations of Ergodic Theory" (Cambridge, 2016)

**Piecewise Isometries:**
- Goetz (2000) "Dynamics of piecewise isometries" - Illinois J. Math.
- Adler, Kitchens, Tresser (2001) "Dynamics of non-ergodic piecewise affine maps of the torus" - Ergodic Theory Dynam. Systems

---

**Last Updated:** 2025-10-17
**Build Status:** ✅ All files compile (verified via check_lean.sh)
**Next Priority:** IntervalExchange.lean lines 208, 244 (unblock 15+ downstream sorries)
**Tool:** Use `./check_lean.sh --errors-only <file>` for all proof testing
