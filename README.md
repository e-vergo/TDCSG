# TDCSG - Piecewise Isometries Formalization

## Current Status

**Remaining Sorries:** 18 across 3 files
**Build Status:** ✅ All files compile with zero errors

### Files by Status

**Complete (0 sorries):**
- [TDCSG/Basic.lean](TDCSG/Basic.lean) - Core `PiecewiseIsometry` structure definition
- [TDCSG/Properties.lean](TDCSG/Properties.lean) - Basic properties and lemmas
- [TDCSG/MeasurePreserving.lean](TDCSG/MeasurePreserving.lean) - Measure-theoretic properties (unprovable theorems removed with counter-examples documented)
- [TDCSG/Composition.lean](TDCSG/Composition.lean) - Category structure, iterate_finite_discontinuities proven with injectivity hypothesis
- [TDCSG/Finite.lean](TDCSG/Finite.lean) - Finite partition specializations (unprovable theorem removed with documentation)

**In Progress:**
- [TDCSG/IntervalExchange.lean](TDCSG/IntervalExchange.lean) - **8 sorries** - All TODO/research placeholders, core infrastructure complete
- [TDCSG/Examples.lean](TDCSG/Examples.lean) - **6 sorries** - 2 impossible (documented), 4 research-level
- [TDCSG/Ergodic.lean](TDCSG/Ergodic.lean) - **4 sorries** - All research-level, ergodic_of_minimal 40% complete

---

## Critical Blockers

### Ergodic.lean:672 - `ergodic_of_minimal` (HIGH PRIORITY - 40% COMPLETE)

**Challenge:** Prove minimal piecewise isometries are ergodic with respect to regular probability measures.

**Current Theorem Statement:**
```lean
theorem ergodic_of_minimal [OpensMeasurableSpace α] [BorelSpace α]
    [μ.WeaklyRegular]
    (f : MinimalPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Ergodic f.toFun μ
```

**Proof Strategy:** Walters Theorem 6.11 - contradiction via outer regularity
**Status:** Lines 622-643 complete (establishes 0 < μ(s) < 1 for invariant set)

**Remaining Technical Gaps (3-5 days estimated):**

**Gap (a) - ENNReal Arithmetic [EASY: 1-2 hours]**
- Need: `∃ r : ℝ≥0∞, μ(s) < r ∧ r < 1` given `μ(s) < 1`
- Solution: Use `r = (μ(s) + 1) / 2` with ENNReal division lemmas
- Search: `ENNReal.add_div`, `ENNReal.div_lt_iff`

**Gap (b) - Measure Difference [MEDIUM: 4-6 hours]**
- Need: Show `μ(U \ s) > 0` when `s ⊆ U` and `μ(s) < μ(U)`
- Requires: `μ(U \ s) = μ(U) - μ(s)` for measurable sets
- Search: `Measure.measure_diff`, `MeasurableSet.diff`

**Gap (c) - Positive Measure → Nonempty [MEDIUM: 4-6 hours]**
- Need: `μ(s) > 0` implies `s.Nonempty` for measurable sets
- Search: `Measure.nonempty_of_measure_ne_zero`, `exists_mem_of_measure_ne_zero`

**Gap (d) - Non-Open Set Dense Orbit [HARD: 1-2 days]** ⚠️ CRITICAL
- **THE KEY BLOCKER**
- Problem: `U \ s` need not be open (s is only measurable, not closed)
- Cannot directly apply `Dense.exists_mem_open` to hit `U \ s`
- **Solution Path 1:** Use `WeaklyRegular.innerRegular` to approximate s by closed K, then `U \ K` is open
  ```lean
  have ⟨K, hK_closed, hKs, hμ_approx⟩ := WeaklyRegular.innerRegular ...
  have h_UK_open : IsOpen (U \ K) := IsOpen.sdiff hU_open hK_closed
  ```
- **Solution Path 2:** Use measure-theoretic essential density instead of topological density
- Search: `WeaklyRegular.innerRegular`, `InnerRegular.exists_compact_subset`, `IsOpen.sdiff`

**Gap (e) - Forward Invariance [MEDIUM: 4-8 hours]**
- Need: `f⁻¹(s) = s` implies `x ∈ s → f^[n](x) ∈ s` for all n
- For bijections: `f⁻¹(s) = s` iff `f(s) = s`, then iterate
- Search: `Function.Bijective.preimage_eq_iff_eq_image`, `Function.iterate_succ`

**Documented in file:** Lines 614-672 contain complete proof structure and gap documentation

---

### IntervalExchange.lean - 8 TODO Placeholders

All core IET infrastructure is **COMPLETE:**
- ✅ `toPiecewiseIsometry` (line 618) - Converts IET to PiecewiseIsometry ℝ
- ✅ `toFinitePiecewiseIsometry` (line 700) - Converts to finite variant
- ✅ `intervals_cover` - Partition coverage proven
- ✅ `intervals_disjoint` - Disjointness proven
- ✅ Interval injectivity - Equal intervals imply equal indices

**Remaining sorries are all TODO comments or research placeholders:**
- Line 735: MeasureSpace instance issue
- Line 743: Nat.pred_lt type mismatch
- Line 748: Standard IET theory construction
- Line 774: toFun field notation + HMod ℝ ℕ ℝ
- Line 779: Irrational and IsUniquelyErgodic definitions missing
- Line 793: MeasureSpace instance + measure_zero_of_finite
- Line 798: Ambiguous term interpretation
- Line 818: toFun field notation

**Action:** These are low-priority cleanup tasks, not critical blockers.

---

### Examples.lean - 6 Sorries

**Lines 350, 361 - DOCUMENTED AS IMPOSSIBLE**
- `double_rotation.isometry_on_pieces` and related
- **Reason:** Metric mismatch - `ℝ × ℝ` uses sup metric, rotations preserve L2 metric
- **Resolution:** Correct version `double_rotation_euclidean` implemented (lines 359-520) using `PiLp 2`
- **Action:** Leave as-is for documentation purposes

**Lines 202, 210, 1092 - RESEARCH-LEVEL**
- `simple_two_IET_discontinuity`: Requires detailed partition structure analysis
- `simple_two_IET_is_rotation`: Requires detailed toFun behavior analysis
- `two_IET_period_two`: Requires detailed IET composition analysis
- **Action:** These require advanced IET theory beyond current Mathlib scope

---

## Proven Strategies

### Pattern: Dependent Type Equality
**Challenge:** Proving sums equal when index types differ by equality proof
**Approach:** Use `Fintype.sum_equiv` with explicit `Equiv` or `OrderIso`
```lean
symm
apply Fintype.sum_equiv ((Fin.castOrderIso hi_succ_eq_n) : Fin i.val.succ ≃ Fin n).symm
intro k
congr 1
```
**Example:** IntervalExchange.lean:270-275 (intervals_cover proof)

### Pattern: Set Extensionality for Intervals
**Challenge:** Proving `Ico a b = Ico c d` implies `a = c` when intervals nonempty
**Approach:** Show left endpoint is in both intervals, extract bounds, use `le_antisymm`
```lean
have h_left_i_mem : domainLeft i ∈ Ico (domainLeft i) (domainRight i) := Set.left_mem_Ico ...
rw [heq] at h_left_i_mem  -- Now in Ico (domainLeft j) (domainRight j)
have h_left_j_mem : domainLeft j ∈ Ico (domainLeft j) (domainRight j) := Set.left_mem_Ico ...
rw [← heq] at h_left_j_mem  -- Now in Ico (domainLeft i) (domainRight i)
-- Extract: domainLeft j ≤ domainLeft i and domainLeft i ≤ domainLeft j
exact le_antisymm h_left_j_mem.1 h_left_i_mem.1
```
**Example:** IntervalExchange.lean:586-596 (interval injectivity)

### Pattern: Fin Sum Inequalities
**Challenge:** Prove partial sum ≤ total sum for `Fin` types
**Approach:** Use `Fin.sum_univ_castSucc` + `castLE` + `Finset.sum_le_sum_of_subset_of_nonneg`
```lean
have h_le : i.val.succ ≤ j.val := Nat.succ_le_of_lt hij
calc ∑ k : Fin i.val, lengths k + lengths i
  _ = ∑ k : Fin i.val.succ, lengths (castLE h_le k) := Fin.sum_univ_castSucc
  _ ≤ ∑ k : Fin j.val, lengths k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _
    · intro; positivity
```
**Example:** IntervalExchange.lean:310-342 (domainRight_le_domainLeft_of_lt)

### Pattern: Isometry on Extended Partitions
**Challenge:** Prove piecewise function is isometry on each piece
**Approach:** Case split on partition (natural pieces vs. boundary pieces), prove separately
```lean
cases hs with
| inl hs_interval =>
  -- Natural piece: translation, use toFun_on_interval lemma
  obtain ⟨i, rfl⟩ := hs_interval
  rw [toFun_on_interval i x hx, toFun_on_interval i y hy]
  simp [dist_comm, Real.dist_eq]; ring_nf
| inr hs_boundary =>
  -- Boundary piece: identity map
  rw [toFun_outside_unit_interval x ..., toFun_outside_unit_interval y ...]
  exact dist_self_eq_zero.symm
```
**Example:** IntervalExchange.lean:658-690 (toPiecewiseIsometry.isometry_on_pieces)

### Pattern: Rotation Matrix L2 Preservation
**Challenge:** Prove rotation matrices preserve Euclidean distance in `PiLp 2`
**Approach:** Use `PiLp.dist_sq_eq_of_L2`, expand rotation algebraically, apply `cos²θ + sin²θ = 1`
```lean
rw [PiLp.dist_sq_eq_of_L2]
simp only [PiLp.sub_apply, Fin.sum_univ_two]
-- Expand: (cos θ Δx - sin θ Δy)² + (sin θ Δx + cos θ Δy)²
ring_nf
-- Simplify using Real.cos_sq_add_sin_sq
rw [← PiLp.dist_sq_eq_of_L2]
```
**Example:** Examples.lean:485-510, 512-537

---

## Key Mathematical Insights

**IET Design Pattern:** Extend IET map to identity outside natural domain [0,1) to satisfy PiecewiseIsometry's requirement that partition covers Set.univ (all of ℝ). Extended partition = `range interval ∪ {Iio 0, Ici 1}`.

**Measure Regularity Bridge:** `WeaklyRegular` hypothesis is essential for connecting topological properties (open sets, dense orbits) with measure-theoretic properties (invariant sets, ergodicity). Provides outer approximation by open sets and inner approximation by closed sets.

**Injectivity for Discontinuities:** Proving `disc(f^[n])` finite when `disc(f)` finite requires injectivity hypothesis. Counter-example: constant maps have infinite preimages of finite sets. For piecewise isometries, injectivity is natural since each piece is an isometry (hence injective).

**Type-Level Metric Consistency:** Isometries must preserve the metric defined at the type level. `ℝ × ℝ` has default sup metric; for Euclidean geometry use `PiLp 2 (Fin 2 → ℝ)` which has L2 metric at type level.

**domainLeft Strict Monotonicity:** For IET, `domainLeft i < domainLeft j` when `i < j` because all lengths positive. This makes intervals have distinct left endpoints, enabling interval injectivity proof via `le_antisymm` on left endpoints.

---

## Essential Resources

### Mathlib Files - Core Imports

**Measure Regularity (CRITICAL for Ergodic.lean):**
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
  - `Measure.WeaklyRegular` - outer/inner approximation type class
  - `WeaklyRegular.innerRegular` - approximate by closed sets
  - `Measure.OuterRegular.outerRegular` - approximate by open sets

**Ergodic Theory:**
- `.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Ergodic.lean`
  - `Ergodic` - definition and basic properties
  - `ergodic_iff_invariant_measure` - characterization via invariant sets
  - `PreErgodic.measure_self_or_compl_eq_zero` - alternative characterization

**Minimal Dynamics:**
- `.lake/packages/mathlib/Mathlib/Dynamics/Minimal.lean`
  - `Minimal` - dense orbits definition
  - Connection between topological and measure-theoretic dynamics

**Dense Sets:**
- `.lake/packages/mathlib/Mathlib/Topology/Dense.lean`
  - `Dense.exists_mem_open` - dense sets hit every nonempty open set
  - Critical for ergodic_of_minimal proof (Gap d)

**Finite Sums over Fin:**
- `.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean`
  - `Fin.sum_univ_castSucc` - relate sum over `Fin n` to `Fin (n+1)`
  - `Finset.sum_le_sum_of_subset_of_nonneg` - monotonicity

**Interval Sets:**
- `.lake/packages/mathlib/Mathlib/Data/Set/Intervals/Basic.lean`
  - `Set.left_mem_Ico` - left endpoint membership
  - `Set.mem_Ico` - interval membership characterization

**PiLp Norms:**
- `.lake/packages/mathlib/Mathlib/Analysis/NormedSpace/PiLp.lean`
  - `PiLp.dist_sq_eq_of_L2` - distance as sum of squared differences
  - Essential for rotation matrix proofs

### Critical Lemmas

**`Fintype.sum_equiv`** - Convert sum over equivalent types
```lean
Fintype.sum_equiv (e : α ≃ β) (f : β → M) = ∑ x : α, f (e x)
```
Use when proving sums equal across type equality.

**`Set.disjoint_iff`** - Convert disjointness to intersection empty
```lean
Disjoint s t ↔ s ∩ t = ∅
```
Use for contradiction when element in both sets.

**`le_antisymm`** - Prove equality from both inequalities
```lean
a ≤ b → b ≤ a → a = b
```
Essential pattern for interval endpoint equality.

**`Real.cos_sq_add_sin_sq`** - Fundamental trigonometric identity
```lean
cos θ ^ 2 + sin θ ^ 2 = 1
```
Core of rotation matrix isometry proofs.

### External References

**Walters "An Introduction to Ergodic Theory" (1982):**
- Theorem 6.11 (Chapter 6): Minimal systems are ergodic with respect to regular probability measures
- Proof strategy: Outer regularity + dense orbits + invariance contradiction
- Critical for Ergodic.lean:672

**Keane "Interval Exchange Transformations" (1975):**
- Unique ergodicity of IETs with irrational data
- Connection: minimality + unique ergodicity
- Referenced in Ergodic.lean:522

**Masur (1982) & Veech (1982) - IET Ergodic Theory:**
- Requires Teichmüller theory, Rauzy-Veech induction
- Multi-year formalization project
- Documented as impossible at Ergodic.lean:391

---

## Next Steps for Successor Agent

### Immediate Actions

1. **Attack Ergodic.lean:672 - Gap (d) - HIGHEST PRIORITY**
   - File: `TDCSG/Ergodic.lean`, lines 645-672
   - **Concrete Task:** Resolve non-open set issue using inner regularity
   - **Approach:**
     ```lean
     -- After obtaining open U ⊇ s with μ(U) < r (line ~655)
     have ⟨K, hK_closed, hKs, hμ_approx⟩ := WeaklyRegular.innerRegular s (measurable s) ...
     have h_UK_open : IsOpen (U \ K) := IsOpen.sdiff hU_open hK_closed
     -- Now apply Dense.exists_mem_open to orbit hitting U \ K
     ```
   - **Search:** `WeaklyRegular.innerRegular`, `InnerRegular.exists_compact_subset`, `IsClosed.isClosed_compl`
   - **Expected Time:** 1-2 days

2. **Complete Ergodic.lean:672 - Remaining Gaps (a,b,c,e)**
   - Gaps (a), (b), (c): Search for existing Mathlib lemmas (likely exist)
   - Gap (e): Prove forward invariance from preimage invariance
   - **Expected Time:** 1-2 days after Gap (d) resolved
   - **Total for ergodic_of_minimal:** 3-5 days

3. **Research Ergodic.lean:320 - `ergodic_iff_irreducible` Forward Direction**
   - File: `TDCSG/Ergodic.lean`, lines 200-320
   - **Missing Piece:** One key lemma connecting a.e. recurrence to set-wise invariance
   - **Search:** Poincaré recurrence, `Conservative.ae_mem_imp_frequently_image_mem`
   - **Expected Time:** 1-2 weeks if lemma exists or can be proven

### Research Priorities

1. **Search for Measure Theory Lemmas (ergodic_of_minimal completion):**
   - Query: `"positive measure" "nonempty"` or `exists_mem_of_measure_ne_zero`
   - Query: `"measure" "difference" "measurable"` or `Measure.measure_diff`
   - Query: `"ENNReal" "between"` or `ENNReal.exists_between`
   - **Tool:** `leansearch` for natural language, `lean_loogle` for type signatures (RATE LIMIT: 3/30s)

2. **Explore Inner Regularity (critical for Gap d):**
   - Read: `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
   - Understand: `InnerRegular`, `WeaklyRegular`, `Regular` hierarchy
   - Find: Lemmas for approximating measurable sets by closed sets
   - **Key Pattern:** Regular measures allow sandwiching measurable sets between closed and open

3. **Study Dense Orbit Lemmas:**
   - Read: `.lake/packages/mathlib/Mathlib/Topology/Dense.lean`
   - Find: Connections between `Dense` and hitting open sets
   - Understand: `dense_iff_closure_eq`, `Dense.exists_mem_open`

### Strategic Approach

**Priority Order:**
1. Ergodic.lean:672 (`ergodic_of_minimal`) - 40% done, clear 3-5 day path, HIGH IMPACT
2. Ergodic.lean:320 (`ergodic_iff_irreducible` forward) - 1-2 weeks if key lemma found
3. IntervalExchange.lean TODO cleanup - low priority, not blocking anything
4. Examples.lean research sorries - defer or axiomatize

**High-Value Targets:**
- **ergodic_of_minimal:** Completing this is a significant ergodic theory result, demonstrates Mathlib adequacy for advanced dynamics
- **ergodic_iff_irreducible forward:** Would complete bidirectional ergodicity characterization

**Defer/Axiomatize:**
- Ergodic.lean:391 (Masur-Veech) - requires multi-year Teichmüller theory formalization
- Ergodic.lean:522 (Keane) - requires 1-2 months ergodic decomposition work
- Examples.lean:202,210,1092 - advanced IET theory beyond current scope

**File Attack Order:**
1. **Ergodic.lean** first - ergodic_of_minimal is 40% done with clear roadmap
2. **IntervalExchange.lean** - cleanup TODO comments (low priority)
3. **Examples.lean** - document remaining as research-level or defer

---

## Technical Notes

### Type Class Requirements

**For Ergodic Theory Proofs:**
- `[OpensMeasurableSpace α]` - open sets are measurable
- `[BorelSpace α]` - measurable sets are Borel σ-algebra
- `[Measure.WeaklyRegular μ]` - outer/inner approximation by open/closed sets
- `[MeasureTheory.IsProbabilityMeasure μ]` - normalized measure (μ(univ) = 1)

**For IET Infrastructure:**
- `[MetricSpace α]` - distance function
- `[MeasurableSpace α]` - σ-algebra structure
- `[BorelSpace α]` - Borel σ-algebra = generated by open sets

### Import Requirements

**Critical for Ergodic.lean:**
```lean
import Mathlib.MeasureTheory.Measure.Regular  -- Line 9, added for WeaklyRegular
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Minimal
```

**Critical for IntervalExchange.lean:**
```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.MetricSpace.Isometry
```

**Critical for Examples.lean:**
```lean
import Mathlib.Analysis.NormedSpace.PiLp  -- For PiLp 2 (Euclidean space)
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic  -- For cos/sin
```

### Build Tool Usage

**Primary Build Verification:**
```bash
./check_lean.sh --errors-only TDCSG/FileName.lean
```
- 99% token reduction vs. raw `lake build`
- Shows complete diagnostics without clipping
- Use after EVERY code change

**Full Diagnostics (when checking warnings):**
```bash
./check_lean.sh TDCSG/FileName.lean
```

**Full Project Build (rare, for major changes):**
```bash
lake build
```

### Lean-LSP MCP Tool Patterns

**Before attacking any sorry:**
1. `lean_goal` at line number - get exact proof obligation
2. `lean_hover` on unfamiliar terms - understand types
3. `lean_try_tactics` with 2-3 different approaches - screen strategies
4. `leansearch` for natural language lemma search
5. `lean_loogle` for type-based search (RATE LIMIT: 3/30s - space calls out!)

**Proof Development Cycle:**
1. Design approach using try_tactics
2. Implement in file
3. Run `./check_lean.sh --errors-only`
4. If errors: read full diagnostic, fix, repeat
5. If success: move to next sorry

---

## Remaining Sorry Inventory

### IntervalExchange.lean (8 sorries)
- `TDCSG/IntervalExchange.lean:735` - TODO: Fix MeasureSpace instance
- `TDCSG/IntervalExchange.lean:743` - TODO: Fix type mismatch with Nat.pred_lt
- `TDCSG/IntervalExchange.lean:748` - Standard construction in IET theory
- `TDCSG/IntervalExchange.lean:774` - TODO: Fix toFun field notation and HMod ℝ ℕ ℝ
- `TDCSG/IntervalExchange.lean:779` - TODO: Fix Irrational and IsUniquelyErgodic
- `TDCSG/IntervalExchange.lean:793` - TODO: Fix MeasureSpace instance and measure_zero_of_finite
- `TDCSG/IntervalExchange.lean:798` - TODO: Fix ambiguous term interpretation
- `TDCSG/IntervalExchange.lean:818` - TODO: Fix toFun field notation

### Examples.lean (6 sorries)
- `TDCSG/Examples.lean:202` - Research-level: simple_two_IET_discontinuity partition analysis
- `TDCSG/Examples.lean:210` - Research-level: simple_two_IET_is_rotation behavior analysis
- `TDCSG/Examples.lean:350` - IMPOSSIBLE: double_rotation sup metric vs L2 metric mismatch (documented)
- `TDCSG/Examples.lean:361` - IMPOSSIBLE: double_rotation_discontinuity (depends on line 350)
- `TDCSG/Examples.lean:1092` - Research-level: two_IET_period_two composition analysis

### Ergodic.lean (4 sorries)
- `TDCSG/Ergodic.lean:320` - ergodic_iff_irreducible (forward direction) - 1-2 weeks with key lemma
- `TDCSG/Ergodic.lean:391` - MASUR-VEECH: Requires years of Teichmüller theory formalization
- `TDCSG/Ergodic.lean:522` - KEANE: Requires 1-2 months ergodic decomposition formalization
- `TDCSG/Ergodic.lean:672` - **ergodic_of_minimal: 40% COMPLETE, 3-5 days to finish, HIGHEST PRIORITY**

**Total Count:** 18 sorries remaining
**Original Count:** 32 sorries
**Completion Status:** 43.75% complete (14 sorries eliminated)

---

**Build Status:** ✅ All files compile successfully
**Last Verified:** 2025-10-17
**Next Priority:** Ergodic.lean:672 Gap (d) - inner regularity for non-open set issue
