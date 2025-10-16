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

/-- Coercion to the underlying piecewise isometry. -/
instance : Coe (MeasurePreservingPiecewiseIsometry α μ) (PiecewiseIsometry α) where
  coe f := f.toPiecewiseIsometry

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
transformations) have null discontinuity sets. -/
theorem measurePreserving_of_null_discontinuities (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_null : μ (f.discontinuitySet) = 0) :
    MeasureTheory.MeasurePreserving f.toFun μ μ := by
  constructor
  · exact h_meas
  · sorry  -- Prove measure equation: μ (f ⁻¹' s) = μ s for measurable s
          -- Strategy: use that f is isometric (hence bijective) on each piece,
          -- and discontinuities have measure zero

/-- If each partition piece has the same measure as its image, the map preserves measure. -/
theorem measurePreserving_of_pieces_preserved (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_pieces : ∀ s ∈ f.partition, μ (f.toFun '' s) = μ s) :
    MeasureTheory.MeasurePreserving f.toFun μ μ := by
  sorry  -- Use piece-by-piece measure preservation

/-- The measure of a preimage of a measurable set can be computed piece-by-piece. -/
theorem measure_preimage_piece (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun) (s : Set α) (hs : MeasurableSet s) :
    μ (f.toFun ⁻¹' s) = ∑' (t : f.partition), μ (t.val ∩ (f.toFun ⁻¹' s)) := by
  sorry  -- Partition the preimage and sum over pieces

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
def id : MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := PiecewiseIsometry.id
  measurable_toFun := measurable_id
  measure_preserving := MeasureTheory.MeasurePreserving.id μ

end Constructors

section Composition

variable {μ : MeasureTheory.Measure α}

/-- Composition of measure-preserving piecewise isometries preserves measure. -/
def comp (f g : MeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f.toPiecewiseIsometry.comp g.toPiecewiseIsometry
  measurable_toFun := f.measurable.comp g.measurable
  measure_preserving := f.measure_preserving.comp g.measure_preserving

/-- Function application for composition. -/
@[simp]
theorem comp_apply (f g : MeasurePreservingPiecewiseIsometry α μ) (x : α) :
    (f.comp g) x = f (g x) := rfl

/-- Composition is associative. -/
theorem comp_assoc (f g h : MeasurePreservingPiecewiseIsometry α μ) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  sorry  -- Follows from composition associativity for piecewise isometries

end Composition

section Iteration

variable {μ : MeasureTheory.Measure α}

/-- The nth iterate of a measure-preserving piecewise isometry. -/
def iterate (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    MeasurePreservingPiecewiseIsometry α μ :=
  match n with
  | 0 => id
  | n + 1 => f.comp (iterate f n)

/-- Notation for iteration. -/
notation:max f "^[" n "]" => iterate f n

/-- Iterate at zero is identity. -/
@[simp]
theorem iterate_zero (f : MeasurePreservingPiecewiseIsometry α μ) :
    f^[0] = id := rfl

/-- Iterate at successor. -/
theorem iterate_succ (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    f^[n + 1] = f.comp (f^[n]) := rfl

/-- Each iterate preserves measure. -/
theorem iterate_preserves_measure (f : MeasurePreservingPiecewiseIsometry α μ) (n : ℕ) :
    MeasureTheory.MeasurePreserving (f^[n]).toFun μ μ :=
  (f^[n]).measure_preserving

end Iteration

section InvariantSets

variable {μ : MeasureTheory.Measure α}

/-- A set is forward-invariant if it is mapped into itself. -/
def IsInvariant (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) : Prop :=
  f.toFun '' s ⊆ s

/-- A set is completely invariant if it is mapped onto itself bijectively. -/
def IsCompletelyInvariant (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) : Prop :=
  f.toFun '' s = s

/-- The measure of an invariant set equals the measure of its image. -/
theorem measure_eq_of_invariant (f : MeasurePreservingPiecewiseIsometry α μ)
    (s : Set α) (hs : MeasurableSet s) (h_inv : IsInvariant f s) :
    μ (f.toFun '' s) = μ s := by
  sorry  -- Use measure preservation

/-- A completely invariant measurable set has the same measure as its preimage. -/
theorem measure_preimage_eq_of_completely_invariant
    (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) (hs : MeasurableSet s)
    (h_inv : IsCompletelyInvariant f s) :
    μ (f.toFun ⁻¹' s) = μ s := by
  sorry  -- Use measure preservation and complete invariance

end InvariantSets

section BorelMeasure

variable [TopologicalSpace α] [BorelSpace α] {μ : MeasureTheory.Measure α}

/-- For Borel measures, isometries on pieces automatically give measurability in many cases. -/
theorem measurable_of_borel (f : PiecewiseIsometry α)
    (h_cont : ∀ s ∈ f.partition, ContinuousOn f.toFun (interior s)) :
    Measurable f.toFun := by
  sorry  -- Use continuity on pieces and null discontinuity set

/-- A piecewise isometry with continuous pieces is measurable with respect to Borel sigma
algebra. -/
theorem borel_measurable_of_continuous_pieces (f : PiecewiseIsometry α)
    (h_open : ∀ s ∈ f.partition, IsOpen (interior s))
    (h_cont : ∀ s ∈ f.partition, ContinuousOn f.toFun s) :
    Measurable f.toFun := by
  sorry  -- Use piecewise continuity

end BorelMeasure

end PiecewiseIsometry
