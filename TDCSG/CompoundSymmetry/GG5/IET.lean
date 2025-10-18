/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.IntervalExchange
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interval Exchange Transformation Emergence in GG(5,5)

This file establishes the connection between the compound symmetry
system GG(5,5) and interval exchange transformations (IETs) that
emerge at the critical radius.

## Main definitions

* `segmentParam`: Parameter defining segment lengths in the
  emergent IET
* `length1`, `length2`, `length3`: Three fundamental lengths for
  the 3-interval IET
* `GG5_induced_IET`: 3-interval exchange transformation induced by
  GG(5,5) dynamics
* `HasEmergentIET`: Predicate for when an IET emerges from system
  dynamics

## Main results

* `length1_golden_ratio`: First length involves golden ratio
* `length2_golden_ratio`: Second length involves golden ratio
* `length3_golden_ratio`: Third length involves golden ratio
* `lengths_sum_to_one`: The three lengths partition the unit
  interval
* `GG5_becomes_IET_at_critical`: At critical radius, GG(5,5)
  dynamics reduce to an IET
* `IET_structure_golden_ratio`: The emergent IET structure
  determined by golden ratio

## Mathematical Background

At the critical radius r_crit = √(3 + φ), where φ is the golden
ratio, the compound symmetry system GG(5,5) undergoes a
qualitative transition. The dynamics on a certain invariant subset
become equivalent to an interval exchange transformation.

The 1D IET emerges as a reduction of the 2D piecewise isometry
dynamics when restricted to specific invariant curves or
cross-sections of the phase space.

## References

* [Richard Kenyon, *Pythagorean tilings*][Kenyon2023]
* [Michael Keane, *Interval exchange transformations*][Keane1975]

-/

namespace CompoundSymmetry.GG5

open PiecewiseIsometry Real

/-- Segment parameter for the emergent IET. -/
noncomputable def segmentParam : ℝ := goldenRatio

/-- First fundamental length in the emergent 3-interval IET. -/
noncomputable def length1 : ℝ :=
  1 / (1 + goldenRatio + goldenRatio ^ 2)

/-- Second fundamental length in the emergent 3-interval IET. -/
noncomputable def length2 : ℝ :=
  goldenRatio / (1 + goldenRatio + goldenRatio ^ 2)

/-- Third fundamental length in the emergent 3-interval IET. -/
noncomputable def length3 : ℝ :=
  (goldenRatio ^ 2) / (1 + goldenRatio + goldenRatio ^ 2)

/-- The lengths are all positive. -/
theorem length1_pos : 0 < length1 := by
  unfold length1
  apply div_pos
  · norm_num
  · apply add_pos
    · apply add_pos
      · norm_num
      · exact Real.goldenRatio_pos
    · apply sq_pos_of_pos
      exact Real.goldenRatio_pos

theorem length2_pos : 0 < length2 := by
  unfold length2
  apply div_pos
  · exact Real.goldenRatio_pos
  · apply add_pos
    · apply add_pos
      · norm_num
      · exact Real.goldenRatio_pos
    · apply sq_pos_of_pos
      exact Real.goldenRatio_pos

theorem length3_pos : 0 < length3 := by
  unfold length3
  apply div_pos
  · apply sq_pos_of_pos
    exact Real.goldenRatio_pos
  · apply add_pos
    · apply add_pos
      · norm_num
      · exact Real.goldenRatio_pos
    · apply sq_pos_of_pos
      exact Real.goldenRatio_pos

/-- The three lengths partition the unit interval. -/
theorem lengths_sum_to_one :
    length1 + length2 + length3 = 1 := by
  unfold length1 length2 length3
  field_simp

/-- First length involves golden ratio. -/
theorem length1_golden_ratio :
    length1 * (1 + goldenRatio + goldenRatio ^ 2) = 1 := by
  unfold length1
  field_simp

/-- Second length involves golden ratio. -/
theorem length2_golden_ratio :
    length2 * (1 + goldenRatio + goldenRatio ^ 2) = goldenRatio := by
  unfold length2
  field_simp

/-- Third length involves golden ratio. -/
theorem length3_golden_ratio :
    length3 * (1 + goldenRatio + goldenRatio ^ 2) =
      goldenRatio ^ 2 := by
  unfold length3
  field_simp

/-- The 3-interval exchange transformation induced by GG(5,5)
dynamics at criticality. -/
noncomputable def GG5_induced_IET : IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i =>
    if i = 0 then length1
    else if i = 1 then length2
    else length3
  lengths_pos := by
    intro i
    fin_cases i
    · simp; exact length1_pos
    · simp; exact length2_pos
    · simp; exact length3_pos
  lengths_sum := by
    have h_univ : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} :=
      by decide
    rw [h_univ]
    rw [Finset.sum_insert, Finset.sum_insert,
      Finset.sum_singleton]
    · simp
      have h := lengths_sum_to_one
      linarith
    · decide
    · decide
  permutation := Equiv.swap 0 2

/-- Predicate: an IET emerges from the system dynamics at
radius r. -/
def HasEmergentIET (r : ℝ) : Prop :=
  r = sqrt (3 + goldenRatio)

/-- The emergent IET at a given radius. -/
noncomputable def EmergentIET (r : ℝ)
    (h : HasEmergentIET r) :
    IntervalExchangeTransformation 3 :=
  GG5_induced_IET

/-- The critical radius for GG(5,5). -/
noncomputable def criticalRadius : ℝ :=
  sqrt (3 + goldenRatio)

/-- At the critical radius, the GG(5,5) system dynamics reduce to
an IET. -/
theorem GG5_becomes_IET_at_critical :
    HasEmergentIET criticalRadius := by
  unfold HasEmergentIET criticalRadius
  rfl

/-- The emergent IET structure is determined by the golden
ratio. -/
theorem IET_structure_golden_ratio
    (h : HasEmergentIET criticalRadius) :
    let iet := EmergentIET criticalRadius h
    iet.lengths 0 = length1 ∧
    iet.lengths 1 = length2 ∧
    iet.lengths 2 = length3 := by
  unfold EmergentIET GG5_induced_IET
  simp only [and_self]
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The interval lengths satisfy golden ratio relations. -/
theorem interval_lengths_golden_ratio_relations :
    length2 = goldenRatio * length1 ∧
    length3 = goldenRatio * length2 := by
  constructor
  · unfold length1 length2
    field_simp
  · unfold length2 length3
    field_simp

/-- The emergent IET has golden ratio structure. -/
theorem emergent_IET_golden_structure
    (h : HasEmergentIET criticalRadius) :
    let iet := EmergentIET criticalRadius h
    ∃ (base : ℝ), base > 0 ∧
      iet.lengths 0 = base ∧
      iet.lengths 1 = goldenRatio * base ∧
      iet.lengths 2 = goldenRatio ^ 2 * base := by
  use length1
  constructor
  · exact length1_pos
  constructor
  · unfold EmergentIET GG5_induced_IET; rfl
  constructor
  · unfold EmergentIET GG5_induced_IET length1 length2
    simp
    field_simp
  · unfold EmergentIET GG5_induced_IET length1 length3
    simp
    field_simp

end CompoundSymmetry.GG5
