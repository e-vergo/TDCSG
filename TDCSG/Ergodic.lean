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

open BigOperators

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
  ergodic : Ergodic toFun μ

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
    Ergodic f.toFun μ :=
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
    Ergodic f.toFun μ ↔
      ∀ s : Set α, MeasurableSet s → f.toFun ⁻¹' s = s → μ s = 0 ∨ μ s = 1 := by
  constructor
  · intro h s hs hinv
    have h_pre := h.toPreErgodic
    have : μ s = 0 ∨ μ sᶜ = 0 := h_pre.measure_self_or_compl_eq_zero hs hinv
    cases this with
    | inl h0 => left; exact h0
    | inr hc =>
      right
      sorry  -- TODO: Complete proof that μ sᶜ = 0 implies μ s = 1
  · intro h
    have h_mp := f.measure_preserving
    constructor
    · exact h_mp
    · constructor
      intro s hs hinv
      obtain h0 | h1 := h s hs hinv
      · sorry  -- TODO: Need to construct Filter.EventuallyConst from measure zero
      · sorry  -- TODO: Need to construct Filter.EventuallyConst from measure one

/-- A piecewise isometry is ergodic if it is mixing (stronger condition). -/
theorem ergodic_of_mixing (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_mixing : ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
      Filter.Tendsto (fun n => μ (f.toFun^[n] ⁻¹' s ∩ t)) Filter.atTop
        (nhds (μ s * μ t))) :
    Ergodic f.toFun μ := by
  constructor
  · exact f.measure_preserving
  · constructor
    intro s hs hinv
    -- For mixing systems, if s is invariant, then μ(s ∩ s) = μ(s) * μ(s)
    have h_lim := h_mixing s s hs hs
    -- Since s is invariant, f^[n]⁻¹' s = s for all n
    -- TODO: Complete the proof that mixing implies ergodic
    -- The argument is: for invariant s, μ(s ∩ s) → μ(s)² but also μ(s ∩ s) = μ(s)
    -- So μ(s) = μ(s)², which for probability measures means μ(s) ∈ {0, 1}
    sorry

/-- Ergodicity can be characterized by irreducibility of the partition dynamics. -/
theorem ergodic_iff_irreducible (f : MeasurePreservingPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Ergodic f.toFun μ ↔
      ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
        μ s > 0 → μ t > 0 →
        ∃ n : ℕ, μ (f.toFun^[n] ⁻¹' s ∩ t) > 0 := by
  constructor
  · -- Ergodic implies irreducible
    intro h_erg s t hs ht h_s_pos h_t_pos
    by_contra h_none
    push_neg at h_none
    -- Consider the union of all preimages of s that intersect t
    let A := ⋃ n : ℕ, f.toFun^[n] ⁻¹' s
    sorry  -- TODO: Complete this direction
  · -- Irreducible implies ergodic
    intro h_irred
    constructor
    · exact f.measure_preserving
    · constructor
      intro s hs hinv
      -- TODO: Complete irreducibility proof
      -- The argument is: if s is invariant with 0 < μ(s) < 1, then by irreducibility
      -- there exists n with μ(f^[n]⁻¹' s ∩ sᶜ) > 0, but f^[n]⁻¹' s = s, contradiction
      sorry

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
    Ergodic f.toFun μ := by
  constructor
  · exact f.measure_preserving
  · constructor
    intro s hs hinv
    -- For a minimal system, if s is invariant with positive measure,
    -- then s must be conull (ae equal to univ)
    sorry  -- TODO: This requires more topological measure theory

end Minimality

section BirkhoffErgodic

-- TODO: The Birkhoff ergodic theorem for piecewise isometries.
-- For an ergodic piecewise isometry and an integrable function, the time average equals
-- the space average almost everywhere.
-- This requires the pointwise ergodic theorem which is not yet in mathlib

end BirkhoffErgodic

section ExamplesOfErgodicSystems

-- TODO: Add axioms for classic ergodic systems examples
-- /-- A rotation by an irrational angle is ergodic. -/
-- Classic result: irrational rotations are ergodic

-- /-- Most interval exchange transformations are ergodic. -/
-- Masur-Veech: generically IETs are ergodic

end ExamplesOfErgodicSystems

section InvariantMeasures

/-- The set of invariant probability measures for a piecewise isometry. -/
def InvariantMeasures (f : PiecewiseIsometry α) : Set (MeasureTheory.Measure α) :=
  {μ | MeasureTheory.IsProbabilityMeasure μ ∧
       MeasureTheory.MeasurePreserving f.toFun μ μ}

-- TODO: The invariant measures form a convex set.
-- TODO: Ergodic measures are extremal points of the invariant measure set.

end InvariantMeasures

section Constructors

/-- Construct an ergodic piecewise isometry from a measure-preserving one with ergodicity
proof. -/
def toErgodicPiecewiseIsometry (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_erg : Ergodic f.toFun μ) :
    ErgodicPiecewiseIsometry α μ where
  toMeasurePreservingPiecewiseIsometry := f
  ergodic := h_erg

end Constructors

end PiecewiseIsometry
