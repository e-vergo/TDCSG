/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Composition
import TDCSG.Definitions.MeasurePreserving
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measure-Preserving Piecewise Isometries

This file develops the theory of measure-preserving piecewise isometries, which are piecewise
isometries that additionally preserve a given measure. This is the second tier in the
three-tiered structure pattern.

## Main definitions

See `TDCSG.Definitions.MeasurePreserving` for definitions:
- `MeasurePreservingPiecewiseIsometry α μ`: A piecewise isometry on `α` that preserves the
  measure `μ`
- `IsInvariant`: A set is forward-invariant under the map
- `IsCompletelyInvariant`: A set is mapped onto itself bijectively
- `idMeasurePreserving`: The identity as a measure-preserving piecewise isometry
- `compMP`: Composition of measure-preserving piecewise isometries
- `iterateMP`: Iteration of a measure-preserving piecewise isometry
- `toPiecewiseIsometry_of_measurePreserving`: Constructor from a piecewise isometry

## Main results

- `toMeasurePreserving`: Extract the measure-preserving property
- `measurable`: The function is measurable
- `measure_preimage_piece`: The measure of a preimage can be computed piece-by-piece
- `compMP_apply`: Function application for composition
- `compMP_assoc_fun`: Composition is associative up to functional equality
- `iterateMP_zero`: Iterate at zero is identity
- `iterateMP_succ`: Iterate at successor
- `iterateMP_preserves_measure`: Each iterate preserves measure
- `measure_eq_of_invariant`: Measure of invariant set equals measure of its image
- `measure_preimage_eq_of_completely_invariant`: Measure of preimage of completely invariant set
- `borel_measurable_of_continuous_pieces`: Piecewise continuous implies measurable

## Implementation notes

We use the `extends` mechanism to inherit from `PiecewiseIsometry` while adding measure
preservation conditions. This follows the pattern used in mathlib's ergodic theory module.

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

namespace MeasurePreservingPiecewiseIsometry

variable {μ : MeasureTheory.Measure α}

/-- Extract the measure-preserving property. -/
theorem toMeasurePreserving (f : MeasurePreservingPiecewiseIsometry α μ) :
    MeasureTheory.MeasurePreserving f.toFun μ μ :=
  f.measure_preserving

/-- The function is measurable. -/
theorem measurable (f : MeasurePreservingPiecewiseIsometry α μ) :
    Measurable f.toFun :=
  f.measurable_toFun

/-- Function application. -/
@[simp]
theorem mp_apply (f : MeasurePreservingPiecewiseIsometry α μ) (x : α) :
    f x = f.toFun x := rfl

/-- Extensionality for MeasurePreservingPiecewiseIsometry: two are equal if all their structure
fields are equal. This is a helper lemma for proving equality of two instances when we can show
that all fields (partition, functions, proofs) coincide.

Note: We do NOT claim that function equality alone implies structure equality, as the partition
structures might differ. This lemma requires actual field-by-field equality. -/
@[ext]
theorem ext_fields {f g : MeasurePreservingPiecewiseIsometry α μ}
    (h_pi : f.toPiecewiseIsometry = g.toPiecewiseIsometry) : f = g := by
  cases f with | mk f_pi f_meas f_mp =>
  cases g with | mk g_pi g_meas g_mp =>
  subst h_pi
  -- After substitution, g_meas and g_mp have the right types
  -- And they are equal to f_meas, f_mp by proof irrelevance
  congr

end MeasurePreservingPiecewiseIsometry

section MeasurePreservation

variable {μ : MeasureTheory.Measure α}

/-! ### Removed Theorems

**REMOVED: `measurePreserving_of_null_discontinuities`**

The original theorem claimed that a surjective piecewise isometry with null discontinuities
preserves arbitrary measure μ. This is **mathematically false**.

Counter-example: Let α = ℝ, μ = Dirac measure at 0, f(x) = x+1. Then f is measurable, surjective,
a piecewise isometry with null discontinuities, but μ(f⁻¹({1})) = 1 ≠ 0 = μ({1}).

The theorem would be true for Hausdorff measure of dimension d (using Mathlib's
`Isometry.hausdorffMeasure_image`), but with μ arbitrary, it's false.

A correct version would require specializing to Hausdorff or Lebesgue measure.

**REMOVED: `measurePreserving_of_pieces_preserved`**

This theorem claimed that if μ(f(p)) = μ(p) for each partition piece p, and f is surjective,
then f preserves μ globally. This cannot be proved with the given hypotheses.

The fundamental issue: even knowing μ(f(p)) = μ(p) for each piece, we cannot deduce that f
preserves the measure of arbitrary measurable subsets without additional structure on μ or
stronger hypotheses about f's action on measurable sets within each piece.

For Mathlib submission, these should be specialized to specific measure types where isometry
preservation is already established.
-/

/-- The measure of a preimage of a measurable set can be computed piece-by-piece. -/
theorem measure_preimage_piece (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun) (s : Set α) (hs : MeasurableSet s) :
    μ (f.toFun ⁻¹' s) = ∑' (t : ↑f.partition), μ (↑t ∩ (f.toFun ⁻¹' s)) := by
  -- Express preimage as a union over partition pieces
  have h_union : f.toFun ⁻¹' s = ⋃ (t : ↑f.partition), ↑t ∩ (f.toFun ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Subtype.exists]
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := f.exists_mem_partition x
      exact ⟨t, ht, hxt, hx⟩
    · intro ⟨_, _, hxt, hx⟩
      exact hx
  conv_lhs => rw [h_union]
  -- Use measure_iUnion for pairwise disjoint measurable sets
  haveI : Countable (↑f.partition) := f.partition_countable.to_subtype
  apply MeasureTheory.measure_iUnion
  · -- Pairwise disjoint
    intro i j hij
    apply Set.disjoint_iff_inter_eq_empty.mpr
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨⟨hxi, _⟩, ⟨hxj, _⟩⟩
    -- x ∈ i and x ∈ j but i ≠ j contradicts partition disjointness
    have : (i : Set α) = (j : Set α) := f.unique_partition_piece x i j i.prop j.prop hxi hxj
    exact hij (Subtype.ext this)
  · -- Each piece is measurable
    intro i
    apply MeasurableSet.inter (f.partition_measurable i i.prop)
    exact h_meas hs

end MeasurePreservation

section Composition

variable {μ : MeasureTheory.Measure α}

/-- Function application for composition. -/
@[simp]
theorem compMP_apply [OpensMeasurableSpace α] [BorelSpace α]
    (f g : MeasurePreservingPiecewiseIsometry α μ) (x : α) :
    (MeasurePreservingPiecewiseIsometry.compMP f g).toFun x = f.toFun (g.toFun x) := rfl

/-- Composition is associative up to functional equality.

**NOTE**: Due to the current structure representation (which includes partition information),
the two sides `compMP (compMP f g) h` and `compMP f (compMP g h)` have different partition
refinements and thus are not structurally equal. However, they represent the same function,
which is what matters for applications.

This lemma proves functional associativity. For structural equality, a quotient-based
representation would be required.
-/
theorem compMP_assoc_fun [OpensMeasurableSpace α] [BorelSpace α]
    (f g h : MeasurePreservingPiecewiseIsometry α μ) (x : α) :
    (MeasurePreservingPiecewiseIsometry.compMP
      (MeasurePreservingPiecewiseIsometry.compMP f g) h).toFun x =
    (MeasurePreservingPiecewiseIsometry.compMP f
      (MeasurePreservingPiecewiseIsometry.compMP g h)).toFun x := by
  -- Both sides compose functions in the same order: f ∘ g ∘ h
  simp only [compMP_apply]
  -- Definitionally equal: (f ∘ g) ∘ h = f ∘ (g ∘ h)

end Composition

section Iteration

variable {μ : MeasureTheory.Measure α}

/-- Iterate at zero is identity. -/
@[simp]
theorem iterateMP_zero [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : MeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry.iterateMP f 0 =
      MeasurePreservingPiecewiseIsometry.idMeasurePreserving := rfl

/-- Iterate at successor. -/
theorem iterateMP_succ [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    MeasurePreservingPiecewiseIsometry.iterateMP f (n + 1) =
      MeasurePreservingPiecewiseIsometry.compMP f
        (MeasurePreservingPiecewiseIsometry.iterateMP f n) := rfl

/-- Each iterate preserves measure. -/
theorem iterateMP_preserves_measure [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    MeasureTheory.MeasurePreserving
      (MeasurePreservingPiecewiseIsometry.iterateMP f n).toFun μ μ :=
  (MeasurePreservingPiecewiseIsometry.iterateMP f n).measure_preserving

end Iteration

section InvariantSets

variable {μ : MeasureTheory.Measure α}

/-- The measure of an invariant set equals the measure of its image.

This theorem requires additional structure beyond what's in the basic PiecewiseIsometry definition.
We need that images of measurable sets are measurable, which for standard Borel spaces follows
from the Lusin-Souslin theorem (Mathlib's `MeasurableSet.image_of_measurable_injOn`).
-/
theorem measure_eq_of_invariant [MeasurableSpace.CountablySeparated α] [StandardBorelSpace α]
    (f : MeasurePreservingPiecewiseIsometry α μ)
    (s : Set α) (hs : MeasurableSet s) (_h_inv : MeasurePreservingPiecewiseIsometry.IsInvariant f s)
    (h_bij : Function.Bijective f.toFun) :
    μ (f.toFun '' s) = μ s := by
  -- Use bijectivity to show f⁻¹(f '' s) = s
  have h_preimage_eq : f.toFun ⁻¹' (f.toFun '' s) = s := by
    ext x
    constructor
    · intro hx
      -- x ∈ f⁻¹(f(s)) means f(x) ∈ f(s), so ∃ y ∈ s, f(y) = f(x)
      obtain ⟨y, hy, hfy⟩ := hx
      -- By injectivity (from bijectivity), x = y
      exact h_bij.1 hfy ▸ hy
    · intro hx
      -- x ∈ s implies f(x) ∈ f(s)
      exact ⟨x, hx, rfl⟩

  -- f '' s is measurable by Lusin-Souslin theorem
  have h_image_meas : MeasurableSet (f.toFun '' s) := by
    exact hs.image_of_measurable_injOn f.measurable h_bij.1.injOn

  -- Apply measure preservation
  calc μ (f.toFun '' s)
      = μ (f.toFun ⁻¹' (f.toFun '' s)) := by
          rw [f.measure_preserving.measure_preimage h_image_meas.nullMeasurableSet]
    _ = μ s := by rw [h_preimage_eq]

/-- A completely invariant measurable set has the same measure as its preimage. -/
theorem measure_preimage_eq_of_completely_invariant
    (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) (hs : MeasurableSet s)
    (_h_inv : MeasurePreservingPiecewiseIsometry.IsCompletelyInvariant f s) :
    μ (f.toFun ⁻¹' s) = μ s := by
  -- Directly use measure preservation
  exact f.measure_preserving.measure_preimage hs.nullMeasurableSet

end InvariantSets

section BorelMeasure

variable [TopologicalSpace α] [BorelSpace α] {μ : MeasureTheory.Measure α}

/-- A piecewise isometry with continuous pieces is measurable with respect to Borel sigma
algebra.

**NEEDS MATHLIB**: This is a general result about piecewise continuous functions on countable
partitions. The proof would use:
1. Measurability of continuous functions
2. Countable unions preserve measurability
3. The fact that being continuous on each piece of a partition makes the function measurable

In mathlib, there should be lemmas like "if f is continuous on each set in a countable measurable
partition, then f is measurable". If not, this would be a good addition to mathlib's
MeasureTheory.Constructions.BorelSpace.Basic.

The proof outline:
- For any open set U, we want to show f⁻¹(U) is measurable
- f⁻¹(U) = ⋃_{s ∈ partition} (s ∩ f⁻¹(U))
- Each s ∩ f⁻¹(U) is measurable because f is continuous on s and s is measurable
- Countable union of measurable sets is measurable
-/
theorem borel_measurable_of_continuous_pieces (f : PiecewiseIsometry α)
    (_h_open : ∀ s ∈ f.partition, IsOpen (interior s))
    (h_cont : ∀ s ∈ f.partition, ContinuousOn f.toFun s) :
    Measurable f.toFun := by
  -- Use the fact that piecewise continuous functions are measurable
  -- Strategy: Show that for any open U, f⁻¹(U) is measurable
  apply measurable_of_isOpen
  intro U hU
  -- Express f⁻¹(U) as a countable union over partition pieces
  have h_union : f.toFun ⁻¹' U = ⋃ (s : ↑f.partition), ↑s ∩ f.toFun ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Subtype.exists]
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := f.exists_mem_partition x
      exact ⟨s, hs, hxs, hx⟩
    · intro ⟨s, hs, hxs, hx⟩
      exact hx
  rw [h_union]
  -- Show each piece is measurable
  haveI : Countable (↑f.partition) := f.partition_countable.to_subtype
  apply MeasurableSet.iUnion
  intro ⟨s, hs⟩
  -- For each s ∈ partition, show s ∩ f⁻¹(U) is measurable
  -- By continuity on s, f⁻¹(U) ∩ s is measurable
  obtain ⟨V, hV_open, hV_eq⟩ := (continuousOn_iff'.mp (h_cont s hs)) U hU
  -- hV_eq : f.toFun ⁻¹' U ∩ s = V ∩ s
  rw [Set.inter_comm, hV_eq]
  exact MeasurableSet.inter hV_open.measurableSet (f.partition_measurable s hs)

end BorelMeasure

end PiecewiseIsometry
