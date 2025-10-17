# TDCSG - Piecewise Isometries Formalization

## Current Status

**Remaining Sorries:** 42 across 5 files

### Files by Status

**Complete (0 sorries):**
- `TDCSG/Basic.lean` - Base definitions for piecewise isometries
- `TDCSG/Properties.lean` - Core properties and theorems
- `TDCSG/Finite.lean` - Finite piecewise isometries

**In Progress:**
- `TDCSG/Composition.lean` - 5 sorries remaining - Partition refinement and composition proofs
- `TDCSG/MeasurePreserving.lean` - 3 sorries remaining - Measure preservation under composition
- `TDCSG/Ergodic.lean` - 4 sorries remaining - Deep ergodic theory results
- `TDCSG/IntervalExchange.lean` - 16 sorries remaining - Type errors and missing definitions
- `TDCSG/Examples.lean` - 14 sorries remaining - Blocked on IET infrastructure and metric issues

## Critical Blockers

### IntervalExchange.lean - Build Failures
**Challenge:** Type errors preventing compilation at lines 170, 176, 245, 255
**Missing Pieces:**
- `toPiecewiseIsometry` and `toFinitePiecewiseIsometry` definitions not implemented
- Type mismatch with `Nat.pred_lt` expecting `0 < ?m.5103`
- `HMod ℝ ℕ ℝ` instance missing for rotation
- Field notation `.toFun` not resolving
- `Irrational` and `IsUniquelyErgodic` not found in scope
**Potential Paths:**
- Implement conversion functions from IET to PiecewiseIsometry
- Add proper imports for Irrational (from Mathlib.Data.Real.Irrational)
- Fix modulo operation types for rotation map

### Composition.lean - Line 179
**Challenge:** Proving partition_cover for composed piecewise isometry
**Goal State:** `⊢ ⋃₀ (refinedPartitionPreimage f g) = Set.univ`
**Missing Pieces:** Need to show refined partition from preimages covers entire space
**Potential Paths:** Use that original partitions cover universe and preimage preserves covering

### Composition.lean - Lines 252-266
**Challenge:** Proving isometry_on_pieces for composition
**Goal State:** Isometry property must hold on each refined partition piece
**Missing Pieces:** Need to track how composition preserves distances through partition refinement
**Potential Paths:** Decompose using isometry properties of f and g on their respective pieces

### MeasurePreserving.lean - Line 108
**Challenge:** Proving PiecewiseIsometry equality from function equality
**Goal State:** `f.toFun = g.toFun → f = g`
**Missing Pieces:** Structural equality for PiecewiseIsometry type
**Potential Paths:** May require extensionality axiom or redesign of equality

### MeasurePreserving.lean - Lines 160, 203
**Challenge:** Measure preservation under piecewise isometry
**Goal State:** Proving measure preservation on partition pieces
**Missing Pieces:** Partition-based measure decomposition theory
**Potential Paths:** Use measure restriction to pieces and piece-wise analysis

### Ergodic.lean - Line 302
**Challenge:** Ergodicity of double rotation
**Goal State:** Proving ergodicity for two-parameter rotation
**Missing Pieces:** Multi-parameter ergodic theory
**Potential Paths:** Reduce to known results about toral rotations

### Ergodic.lean - Lines 373, 492, 559
**Challenge:** Deep ergodic theory results
**Missing Pieces:**
- Line 373: Teichmüller theory, Rauzy-Veech induction
- Line 492: Birkhoff ergodic theorem, ergodic decomposition (not in Mathlib)
- Line 559: Measure support theory, Baire category arguments
**Potential Paths:** These require substantial mathematical machinery not yet in Mathlib

### Examples.lean - Metric Configuration
**Challenge:** ℝ × ℝ uses sup metric, but rotations need Euclidean metric
**Goal State:** Rotations preserve Euclidean distance, not sup distance
**Missing Pieces:** Need to use `PiLp 2 (Fin 2 → ℝ)` for L2 metric
**Potential Paths:** Either redesign examples for sup metric or reconfigure type to use Euclidean

## Proven Strategies

**Pattern:** Simple partition coverage proofs
**Approach:** Use `Set.sUnion_eq_univ_iff` and show every point belongs to some piece
**Examples:** Basic.lean lines 77-79

**Pattern:** Isometry within partition pieces
**Approach:** Direct application of hypothesis `isometry_on_pieces`
**Examples:** Basic.lean lines 70-72

**Pattern:** NON_ISOMETRY proofs via pigeonhole
**Approach:** Find uncountable subset mapped to same partition piece, show distance scaling contradicts isometry
**Examples:** Examples.lean line 454 (doubling_map_NON_ISOMETRY - completed by agent)

**Pattern:** Finite Fin sums using decide
**Approach:** For small Fin types, expand using decide and ring
**Examples:** Successfully applied by agents in various proofs

## Key Mathematical Insights

- Piecewise isometries preserve distance within partition pieces but may have discontinuities at boundaries
- Composition requires refined partition from preimages of both maps' partitions
- Interval exchange transformations are special case with intervals as partition pieces
- Ergodicity for piecewise isometries requires irrational rotation angles or complex dynamics
- Measure preservation requires careful analysis on partition boundaries (null sets)

## Essential Resources

**Mathlib Files:**
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean` - Borel measurability
- `.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Basic.lean` - Ergodic theory foundations
- `.lake/packages/mathlib/Mathlib/Data/Real/Irrational.lean` - Irrational numbers
- `.lake/packages/mathlib/Mathlib/Analysis/NormedSpace/PiLp.lean` - Lp norms on product spaces

**Critical Lemmas:**
- `Set.sUnion_eq_univ_iff` - For proving partition coverage
- `MeasurableSet.biUnion` - For measurability of unions
- `Set.PairwiseDisjoint` - For partition disjointness

## Next Steps for Successor Agent

1. **Immediate Actions:**
   - Fix IntervalExchange.lean build errors (add missing imports, fix type mismatches)
   - Complete Composition.lean line 179 using covering property of preimages
   - Prove baker_map_NON_ISOMETRY in Examples.lean using doubling_map pattern

2. **Research Priorities:**
   - Search loogle for "partition refinement" lemmas
   - Search leansearch for "measure preserving piecewise"
   - Research Birkhoff ergodic theorem status in Mathlib
   - Find correct type for Euclidean metric on ℝ²

3. **Strategic Approach:**
   - Priority 1: Fix IntervalExchange.lean compilation (blocks other work)
   - Priority 2: Complete Composition.lean (foundational for MeasurePreserving)
   - Priority 3: Resolve metric issues in Examples.lean
   - Priority 4: Deep ergodic theory results (may need new Mathlib PRs)

## Technical Notes

**Type Class Issues:**
- MeasureSpace instances not resolving in IntervalExchange
- CommSemiring vs CommRing confusion in some proofs
- HMod instance needed for rotation maps

**Import Requirements:**
- Add `import Mathlib.Data.Real.Irrational` to IntervalExchange.lean
- May need `import Mathlib.Analysis.NormedSpace.PiLp` for Examples.lean

**Build Considerations:**
- IntervalExchange.lean must compile before Examples.lean can use IET infrastructure
- Use `lake build TDCSG` to verify global compilation

**Tool Usage Notes:**
- lean_loogle has 3 req/30s rate limit - space out calls
- lean_multi_attempt excellent for testing multiple tactics quickly
- lean_goal essential before each proof attempt

## Remaining Sorry Inventory

- `TDCSG/Composition.lean:179` - partition_cover for composition
- `TDCSG/Composition.lean:252` - partition_disjoint for composition
- `TDCSG/Composition.lean:259` - partition_nonempty for composition
- `TDCSG/Composition.lean:266` - isometry_on_pieces for composition
- `TDCSG/Composition.lean:528` - comp_assoc associativity
- `TDCSG/MeasurePreserving.lean:108` - ext_iff extensionality
- `TDCSG/MeasurePreserving.lean:160` - preserves_measure for piecewise
- `TDCSG/MeasurePreserving.lean:203` - comp_preserves for composition
- `TDCSG/Ergodic.lean:302` - double_rotation_ergodic
- `TDCSG/Ergodic.lean:373` - generic IET ergodicity (deep)
- `TDCSG/Ergodic.lean:492` - Birkhoff theorem application (deep)
- `TDCSG/Ergodic.lean:559` - minimal IET wandering set (deep)
- `TDCSG/IntervalExchange.lean:178` - partition_cover for IET
- `TDCSG/IntervalExchange.lean:187` - partition_disjoint for IET
- `TDCSG/IntervalExchange.lean:245` - toPiecewiseIsometry definition
- `TDCSG/IntervalExchange.lean:255` - toFinitePiecewiseIsometry definition
- `TDCSG/IntervalExchange.lean:260` - IET measurability
- `TDCSG/IntervalExchange.lean:268` - singularities_finite
- `TDCSG/IntervalExchange.lean:273` - two_interval_exchange construction
- `TDCSG/IntervalExchange.lean:299` - rotation_IET definition
- `TDCSG/IntervalExchange.lean:304` - rotation_uniquely_ergodic
- `TDCSG/IntervalExchange.lean:314` - zero_entropy (placeholder)
- `TDCSG/IntervalExchange.lean:318` - singularities_measure_zero (placeholder)
- `TDCSG/IntervalExchange.lean:323` - first_return_map
- `TDCSG/IntervalExchange.lean:343` - induced_IET
- `TDCSG/IntervalExchange.lean:356` - preserves_lebesgue (placeholder)
- `TDCSG/IntervalExchange.lean:361` - aperiodic_iff_ergodic (placeholder)
- `TDCSG/IntervalExchange.lean:365` - recurrent_ae (placeholder)
- `TDCSG/Examples.lean:189` - simple_two_IET_PI definition
- `TDCSG/Examples.lean:198` - simple_two_IET_discontinuity
- `TDCSG/Examples.lean:205` - simple_two_IET_is_rotation
- `TDCSG/Examples.lean:266` - double_rotation partition_cover
- `TDCSG/Examples.lean:298` - double_rotation isometry_on_pieces
- `TDCSG/Examples.lean:306` - double_rotation_discontinuity
- `TDCSG/Examples.lean:410` - square_billiard partition_cover
- `TDCSG/Examples.lean:430` - square_billiard isometry_on_pieces
- `TDCSG/Examples.lean:439` - square_billiard_boundary_discontinuity
- `TDCSG/Examples.lean:521` - baker_map_NON_ISOMETRY
- `TDCSG/Examples.lean:538` - iterated_two_IET definition
- `TDCSG/Examples.lean:544` - two_IET_period_two
- `TDCSG/Examples.lean:619` - FinitePiecewiseIsometry example template

**Total Count:** 42 sorries remaining
**Completion Status:** 14.0% complete (7 sorries eliminated / 49 total sorries at start)