/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Composition
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measure-Preserving Piecewise Isometries

This file develops the theory of measure-preserving piecewise isometries, which are piecewise
isometries that additionally preserve a given measure. This is the second tier in the
three-tiered structure pattern.

## Main definitions

- `MeasurePreservingPiecewiseIsometry α μ`: A piecewise isometry on `α` that preserves the
  measure `μ`
- `MeasurePreservingPiecewiseIsometry.toMeasurePreserving`: Extract the measure-preserving
  property as a `MeasureTheory.MeasurePreserving` instance

## Main results

- `measurePreserving_of_null_discontinuities`: A piecewise isometry with measure-zero
  discontinuities is measure-preserving if measurable
- `measure_preimage_piece`: The measure of a preimage can be computed piece-by-piece
- `comp_preserves_measure`: Composition of measure-preserving piecewise isometries preserves
  measure
- `iterate_preserves_measure`: Iteration of a measure-preserving piecewise isometry preserves
  measure

## Implementation notes

We use the `extends` mechanism to inherit from `PiecewiseIsometry` while adding measure
preservation conditions. This follows the pattern used in mathlib's ergodic theory module.

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

/-- A measure-preserving piecewise isometry.

This structure extends `PiecewiseIsometry` by requiring that the underlying function is
measurable and preserves a specified measure `μ`. -/
structure MeasurePreservingPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends PiecewiseIsometry α where
  /-- The underlying function is measurable -/
  measurable_toFun : Measurable toFun
  /-- The function preserves the measure μ -/
  measure_preserving : MeasureTheory.MeasurePreserving toFun μ μ

namespace MeasurePreservingPiecewiseIsometry

variable {μ : MeasureTheory.Measure α}

/-- Allow function application notation. -/
instance : CoeFun (MeasurePreservingPiecewiseIsometry α μ) (fun _ => α → α) where
  coe f := f.toFun

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
theorem apply_eq_toFun (f : MeasurePreservingPiecewiseIsometry α μ) (x : α) :
    f x = f.toFun x := rfl

end MeasurePreservingPiecewiseIsometry

section MeasurePreservation

variable {μ : MeasureTheory.Measure α}

/-- A key theorem: if a piecewise isometry is measurable and its discontinuity set has
measure zero, then it preserves measure.

This is a fundamental result because many natural piecewise isometries (like interval exchange
transformations) have null discontinuity sets.

**DEEP RESULT**: This theorem requires bijectivity or surjectivity assumptions on f, which are
not part of the basic PiecewiseIsometry structure. The proof would need to show that f is
almost everywhere bijective, which is not automatic from the isometry-on-pieces property alone.
For a complete proof, one would need additional hypotheses like:
- f is surjective, or
- f is injective and μ(α \ range f) = 0, or
- stronger global properties beyond piecewise isometry

This is closely related to the Poincaré recurrence theorem and requires substantial ergodic theory.
-/
theorem measurePreserving_of_null_discontinuities (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_null : μ (f.discontinuitySet) = 0) :
    MeasureTheory.MeasurePreserving f.toFun μ μ := by
  constructor
  · exact h_meas
  · -- Need to prove: ∀ s, MeasurableSet s → μ (f ⁻¹' s) = μ s
    -- This requires additional structure (e.g., f bijective, f surjective, etc.)
    -- For piecewise isometries, this holds when f is almost everywhere bijective
    -- This is a deep result requiring more sophisticated measure theory
    sorry

/-- If each partition piece has the same measure as its image, the map preserves measure.

**DEEP RESULT**: While this looks straightforward, the full proof is subtle. The challenge is to
show that for an arbitrary measurable set t, we have μ(f⁻¹(t)) = μ(t). The natural approach is:
1. Partition t using the images of partition pieces
2. Use that μ(f(s)) = μ(s) for each piece s
3. Relate f⁻¹(t) to the partition pieces

However, step 1 requires understanding how t intersects with f(s) for each piece s, and this
intersection may not have a simple preimage structure unless f is bijective on each piece.
The hypothesis μ(f(s)) = μ(s) gives measure equality but doesn't immediately imply that
f⁻¹(f(s) ∩ t) has the right measure unless f is injective on pieces (which it is) AND
we know something about the range of f. This requires careful measure-theoretic arguments
about images and preimages under piecewise isometries.
-/
theorem measurePreserving_of_pieces_preserved (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_pieces : ∀ s ∈ f.partition, μ (f.toFun '' s) = μ s) :
    MeasureTheory.MeasurePreserving f.toFun μ μ := by
  constructor
  · exact h_meas
  · -- Need to show μ (f ⁻¹' t) = μ t for all measurable t
    -- Partition the preimage and use piece-by-piece preservation
    -- The full proof requires showing that f maps pieces bijectively and using the partition
    sorry

/-- The measure of a preimage of a measurable set can be computed piece-by-piece. -/
theorem measure_preimage_piece (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun) (s : Set α) (hs : MeasurableSet s) :
    μ (f.toFun ⁻¹' s) = ∑' (t : f.partition), μ (t.val ∩ (f.toFun ⁻¹' s)) := by
  -- The preimage can be partitioned as the disjoint union over partition pieces
  -- Use that partition covers univ and is pairwise disjoint
  have h_cover : f.toFun ⁻¹' s = ⋃₀ (Set.image (fun t => t ∩ (f.toFun ⁻¹' s)) f.partition) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_image]
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := f.exists_mem_partition x
      use t ∩ (f.toFun ⁻¹' s), ⟨t, ht, rfl⟩
      exact ⟨hxt, hx⟩
    · intro ⟨_, ⟨t, ht, rfl⟩, hxt, hxs⟩
      exact hxs
  rw [h_cover]
  -- Now apply measure_sUnion for the countable disjoint union
  -- The image of the partition is countable
  have h_image_countable : (Set.image (fun t => t ∩ (f.toFun ⁻¹' s)) f.partition).Countable :=
    f.partition_countable.image _
  -- The image sets are pairwise disjoint
  have h_image_disjoint : (Set.image (fun t => t ∩ (f.toFun ⁻¹' s)) f.partition).Pairwise Disjoint := by
    intro u hu v hv huv
    obtain ⟨tu, htu, rfl⟩ := hu
    obtain ⟨tv, htv, rfl⟩ := hv
    by_cases h : tu = tv
    · rw [h] at huv
      exact absurd rfl huv
    · have hdisj : Disjoint tu tv := f.partition_disjoint htu htv h
      exact Disjoint.inf_left _ (Disjoint.inf_right _ hdisj)
  -- Each piece is measurable
  have h_image_meas : ∀ u ∈ (Set.image (fun t => t ∩ (f.toFun ⁻¹' s)) f.partition), MeasurableSet u := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact (f.partition_measurable t ht).inter (h_meas hs)
  -- Apply measure_sUnion
  rw [MeasureTheory.measure_sUnion h_image_countable h_image_disjoint h_image_meas]
  -- The tsum is over the image, convert to tsum over partition
  sorry -- Need to show bijection between partition and image preserves sum

end MeasurePreservation

section Constructors

variable {μ : MeasureTheory.Measure α}

/-- Construct a measure-preserving piecewise isometry from a piecewise isometry with
additional properties. -/
def toPiecewiseIsometry_of_measurePreserving (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_mp : MeasureTheory.MeasurePreserving f.toFun μ μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f
  measurable_toFun := h_meas
  measure_preserving := h_mp

/-- The identity as a measure-preserving piecewise isometry. -/
def idMeasurePreserving : MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := PiecewiseIsometry.id
  measurable_toFun := measurable_id
  measure_preserving := MeasureTheory.MeasurePreserving.id μ

end Constructors

section Composition

variable {μ : MeasureTheory.Measure α}

/-- Composition of measure-preserving piecewise isometries preserves measure. -/
def compMP (f g : MeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f.toPiecewiseIsometry.comp g.toPiecewiseIsometry
  measurable_toFun := f.measurable.comp g.measurable
  measure_preserving := f.measure_preserving.comp g.measure_preserving

/-- Function application for composition. -/
@[simp]
theorem compMP_apply (f g : MeasurePreservingPiecewiseIsometry α μ) (x : α) :
    (compMP f g).toFun x = f.toFun (g.toFun x) := rfl

/-- Composition is associative. -/
theorem compMP_assoc (f g h : MeasurePreservingPiecewiseIsometry α μ) :
    compMP (compMP f g) h = compMP f (compMP g h) := by
  -- Both sides have the same underlying piecewise isometry due to comp_assoc
  -- and the same measurability and measure preservation properties
  -- However, we need extensionality for MeasurePreservingPiecewiseIsometry
  sorry -- Requires extensionality lemma for the structure

end Composition

section Iteration

variable {μ : MeasureTheory.Measure α}

/-- The nth iterate of a measure-preserving piecewise isometry. -/
def iterateMP (f : MeasurePreservingPiecewiseIsometry α μ) : ℕ → MeasurePreservingPiecewiseIsometry α μ
  | 0 => idMeasurePreserving
  | n + 1 => compMP f (iterateMP f n)

/-- Iterate at zero is identity. -/
@[simp]
theorem iterateMP_zero (f : MeasurePreservingPiecewiseIsometry α μ) :
    iterateMP f 0 = idMeasurePreserving := rfl

/-- Iterate at successor. -/
theorem iterateMP_succ (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    iterateMP f (n + 1) = compMP f (iterateMP f n) := rfl

/-- Each iterate preserves measure. -/
theorem iterateMP_preserves_measure (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    MeasureTheory.MeasurePreserving (iterateMP f n).toFun μ μ :=
  (iterateMP f n).measure_preserving

end Iteration

section InvariantSets

variable {μ : MeasureTheory.Measure α}

/-- A set is forward-invariant if it is mapped into itself. -/
def IsInvariant (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) : Prop :=
  f.toFun '' s ⊆ s

/-- A set is completely invariant if it is mapped onto itself bijectively. -/
def IsCompletelyInvariant (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) : Prop :=
  f.toFun '' s = s

/-- The measure of an invariant set equals the measure of its image.

**DEEP RESULT**: This requires showing that for an invariant set s (where f(s) ⊆ s), we have
μ(f(s)) = μ(s). The natural approach is to use measure preservation: μ(f⁻¹(f(s))) = μ(f(s)).
Then we want to show f⁻¹(f(s)) = s. We know:
- f is injective on each partition piece, so f⁻¹(f(s)) ⊇ s
- f(s) ⊆ s by invariance, so f⁻¹(f(s)) ⊆ f⁻¹(s)

But f⁻¹(s) may be larger than s in general unless f is surjective. The gap is that injectivity
on pieces doesn't give global surjectivity. We need either:
- f to be surjective globally, or
- Additional structure showing μ(f⁻¹(s) \ s) = 0

This is technically solvable but requires more sophisticated arguments about piecewise isometries.
-/
theorem measure_eq_of_invariant (f : MeasurePreservingPiecewiseIsometry α μ)
    (s : Set α) (hs : MeasurableSet s) (h_inv : IsInvariant f s) :
    μ (f.toFun '' s) = μ s := by
  -- Use measure preservation: μ(f⁻¹(f(s))) = μ(f(s))
  -- Since f is injective on pieces, f⁻¹(f(s)) = s
  -- Requires complex reasoning about injectivity and preimages
  sorry

/-- A completely invariant measurable set has the same measure as its preimage. -/
theorem measure_preimage_eq_of_completely_invariant
    (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) (hs : MeasurableSet s)
    (h_inv : IsCompletelyInvariant f s) :
    μ (f.toFun ⁻¹' s) = μ s := by
  -- Directly use measure preservation
  exact f.measure_preserving.measure_preimage hs.nullMeasurableSet

end InvariantSets

section BorelMeasure

variable [TopologicalSpace α] [BorelSpace α] {μ : MeasureTheory.Measure α}

/-- For Borel measures, isometries on pieces automatically give measurability in many cases.

**NEEDS MATHLIB**: This theorem is provable but requires results about measurability of
piecewise continuous functions that may not yet be in mathlib in the needed generality.
The key ingredients needed are:
1. A function continuous on the interior of partition pieces is measurable
2. The discontinuity set (frontiers of pieces) has measure zero or is negligible
3. Borel measurability for functions that are continuous a.e.

The proof strategy would be:
- Show f is continuous on ⋃ interior(s) for s in partition
- This set has full measure (complement is the discontinuity set)
- Use that functions continuous a.e. are measurable in Borel spaces

This should be straightforward once the right mathlib lemmas are identified.
-/
theorem measurable_of_borel (f : PiecewiseIsometry α)
    (h_cont : ∀ s ∈ f.partition, ContinuousOn f.toFun (interior s)) :
    Measurable f.toFun := by
  -- For now, we admit this as it requires more sophisticated measure theory
  -- The key idea: continuous on pieces with null discontinuity set implies measurable
  sorry

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
    (h_open : ∀ s ∈ f.partition, IsOpen (interior s))
    (h_cont : ∀ s ∈ f.partition, ContinuousOn f.toFun s) :
    Measurable f.toFun := by
  -- Piecewise continuous functions on a countable partition are measurable
  sorry

end BorelMeasure

end PiecewiseIsometry
