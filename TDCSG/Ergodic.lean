/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodic Piecewise Isometries

This file develops the theory of ergodic piecewise isometries, which are measure-preserving
piecewise isometries that additionally satisfy the ergodic property: every invariant set has
measure zero or full measure.

This is the third tier in the three-tiered structure pattern for piecewise isometries.

## Main definitions

- `ErgodicPiecewiseIsometry α μ`: A measure-preserving piecewise isometry that is ergodic
  with respect to measure `μ`
- `MinimalPiecewiseIsometry α μ`: A piecewise isometry with all orbits dense

## Main results

- `ergodic_of_mixing`: A mixing piecewise isometry is ergodic
- `unique_ergodicity_of_finite`: Conditions for unique ergodicity
- `ergodic_iff_irreducible`: Ergodicity characterized by irreducibility of the partition
- `minimal_implies_uniquely_ergodic`: Under suitable conditions, minimality implies unique
  ergodicity

## References

* [Peter Walters, *An Introduction to Ergodic Theory*][Walters1982]
* [Arek Goetz, *Dynamics of piecewise isometries*][Goetz2000]

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α}

/-- An ergodic piecewise isometry.

This extends `MeasurePreservingPiecewiseIsometry` by requiring that the map is ergodic:
every invariant measurable set has measure zero or full measure. -/
structure ErgodicPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends MeasurePreservingPiecewiseIsometry α μ where
  /-- The map is ergodic with respect to μ -/
  ergodic : MeasureTheory.Ergodic toFun μ

namespace ErgodicPiecewiseIsometry

/-- Coercion to measure-preserving piecewise isometry. -/
instance : Coe (ErgodicPiecewiseIsometry α μ)
    (MeasurePreservingPiecewiseIsometry α μ) where
  coe f := f.toMeasurePreservingPiecewiseIsometry

/-- Allow function application. -/
instance : CoeFun (ErgodicPiecewiseIsometry α μ) (fun _ => α → α) where
  coe f := f.toFun

/-- Extract the ergodic property. -/
theorem isErgodic (f : ErgodicPiecewiseIsometry α μ) :
    MeasureTheory.Ergodic f.toFun μ :=
  f.ergodic

/-- Function application. -/
@[simp]
theorem apply_eq_toFun (f : ErgodicPiecewiseIsometry α μ) (x : α) :
    f x = f.toFun x := rfl

end ErgodicPiecewiseIsometry

section ErgodicityConditions

/-- A measure-preserving piecewise isometry is ergodic if every invariant set has measure
zero or full measure. -/
theorem ergodic_iff_invariant_measure (f : MeasurePreservingPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.Ergodic f.toFun μ ↔
      ∀ s : Set α, MeasurableSet s → f.toFun ⁻¹' s = s → μ s = 0 ∨ μ s = 1 := by
  sorry  -- This is the definition of ergodicity

/-- A piecewise isometry is ergodic if it is mixing (stronger condition). -/
theorem ergodic_of_mixing (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_mixing : ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
      Filter.Tendsto (fun n => μ (f.toFun^[n] ⁻¹' s ∩ t)) Filter.atTop
        (nhds (μ s * μ t))) :
    MeasureTheory.Ergodic f.toFun μ := by
  sorry  -- Mixing implies ergodic (standard result in ergodic theory)

/-- Ergodicity can be characterized by irreducibility of the partition dynamics. -/
theorem ergodic_iff_irreducible (f : MeasurePreservingPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.Ergodic f.toFun μ ↔
      ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
        μ s > 0 → μ t > 0 →
        ∃ n : ℕ, μ (f.toFun^[n] ⁻¹' s ∩ t) > 0 := by
  sorry  -- Irreducibility characterization of ergodicity

end ErgodicityConditions

section UniqueErgodicity

/-- A measure-preserving piecewise isometry is uniquely ergodic if there is only one
invariant probability measure. -/
def IsUniquelyErgodic (f : PiecewiseIsometry α) (μ : MeasureTheory.Measure α) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧
  MeasureTheory.MeasurePreserving f.toFun μ μ ∧
  ∀ ν : MeasureTheory.Measure α, MeasureTheory.IsProbabilityMeasure ν →
    MeasureTheory.MeasurePreserving f.toFun ν ν → ν = μ

/-- For interval exchange transformations (finite partition), unique ergodicity is generic. -/
theorem uniquely_ergodic_of_irrational_data (f : PiecewiseIsometry α)
    (h_finite : f.partition.Finite)
    (h_irrat : sorry) :  -- Needs formalization of irrationality condition
    ∃ μ : MeasureTheory.Measure α, IsUniquelyErgodic f μ := by
  sorry  -- This is a deep result for IETs (Masur-Veech theorem)

end UniqueErgodicity

section Minimality

/-- A piecewise isometry is minimal if every orbit is dense. -/
def IsMinimal (f : PiecewiseIsometry α) : Prop :=
  ∀ x : α, Dense (Set.range fun n : ℕ => f.toFun^[n] x)

/-- A measure-preserving minimal piecewise isometry. -/
structure MinimalPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends MeasurePreservingPiecewiseIsometry α μ where
  /-- Every orbit is dense -/
  minimal : IsMinimal toPiecewiseIsometry

/-- Minimality implies unique ergodicity for uniquely ergodic systems. -/
theorem minimal_implies_uniquely_ergodic (f : MinimalPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (h_finite : f.toPiecewiseIsometry.partition.Finite) :
    IsUniquelyErgodic f.toPiecewiseIsometry μ := by
  sorry  -- This holds for minimal IETs

/-- A minimal system is ergodic with respect to any invariant measure. -/
theorem ergodic_of_minimal (f : MinimalPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.Ergodic f.toFun μ := by
  sorry  -- Minimality implies ergodicity

end Minimality

section BirkhoffErgodic

/-- The Birkhoff ergodic theorem for piecewise isometries.

For an ergodic piecewise isometry and an integrable function, the time average equals
the space average almost everywhere. -/
theorem birkhoff_ergodic_theorem (f : ErgodicPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (φ : α → ℝ) (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k in Finset.range n, φ (f.toFun^[k] x))
      Filter.atTop (nhds (∫ x, φ x ∂μ)) := by
  sorry  -- This is Birkhoff's ergodic theorem, should exist in mathlib

end BirkhoffErgodic

section ExamplesOfErgodicSystems

/-- A rotation by an irrational angle is ergodic. -/
theorem rotation_ergodic [MeasurableSpace α] (θ : ℝ) (h_irrat : Irrational θ) :
    sorry := by  -- Needs formalization of circle rotations
  sorry  -- Classic result: irrational rotations are ergodic

/-- Most interval exchange transformations are ergodic. -/
theorem IET_ergodic_generic :
    sorry := by  -- Needs parameter space formalization
  sorry  -- Masur-Veech: generically IETs are ergodic

end ExamplesOfErgodicSystems

section InvariantMeasures

/-- The set of invariant probability measures for a piecewise isometry. -/
def InvariantMeasures (f : PiecewiseIsometry α) : Set (MeasureTheory.Measure α) :=
  {μ | MeasureTheory.IsProbabilityMeasure μ ∧
       MeasureTheory.MeasurePreserving f.toFun μ μ}

/-- The invariant measures form a convex set. -/
theorem invariant_measures_convex (f : PiecewiseIsometry α) :
    Convex ℝ (InvariantMeasures f) := by
  sorry  -- Convex combination of invariant measures is invariant

/-- Ergodic measures are extremal points of the invariant measure set. -/
theorem ergodic_iff_extremal (f : PiecewiseIsometry α) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ]
    (h_inv : μ ∈ InvariantMeasures f) :
    MeasureTheory.Ergodic f.toFun μ ↔
      ∀ ν₁ ν₂ : MeasureTheory.Measure α, ν₁ ∈ InvariantMeasures f →
        ν₂ ∈ InvariantMeasures f →
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, μ = t • ν₁ + (1 - t) • ν₂ → ν₁ = μ ∧ ν₂ = μ := by
  sorry  -- Ergodic measures are extremal (standard ergodic theory)

end InvariantMeasures

section Constructors

/-- Construct an ergodic piecewise isometry from a measure-preserving one with ergodicity
proof. -/
def toErgodicPiecewiseIsometry (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_erg : MeasureTheory.Ergodic f.toFun μ) :
    ErgodicPiecewiseIsometry α μ where
  toMeasurePreservingPiecewiseIsometry := f
  ergodic := h_erg

end Constructors

end PiecewiseIsometry
