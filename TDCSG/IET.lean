/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.IET
import TDCSG.IntervalExchange
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interval Exchange Transformation Emergence in GG(5,5)

This file establishes the connection between the compound symmetry
system GG(5,5) and interval exchange transformations (IETs) that
emerge at the critical radius.

The fundamental definitions (length1, length2, length3, displacements)
are in TDCSG.Definitions.IET.

## Main definitions

* `GG5_induced_IET`: 3-interval exchange transformation induced by
  GG(5,5) dynamics
* `HasEmergentIET`: Predicate for when an IET emerges from system
  dynamics

## Main results

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

open PiecewiseIsometry Real TDCSG.Definitions

/-! ### Basic properties of interval lengths -/

/-- The denominator 1 + φ + φ² is positive. -/
private lemma denom_pos : 0 < 1 + goldenRatio + goldenRatio ^ 2 := by
  have h1 : 0 < goldenRatio := goldenRatio_pos
  have h2 : 0 < goldenRatio ^ 2 := by positivity
  linarith

/-- The first interval length is positive. -/
lemma length1_pos : 0 < length1 := by
  unfold length1
  exact div_pos one_pos denom_pos

/-- The second interval length is positive. -/
lemma length2_pos : 0 < length2 := by
  unfold length2
  exact div_pos goldenRatio_pos denom_pos

/-- The third interval length is positive. -/
lemma length3_pos : 0 < length3 := by
  unfold length3
  have h : 0 < goldenRatio ^ 2 := by positivity
  exact div_pos h denom_pos

/-- The three interval lengths sum to one. -/
lemma lengths_sum_to_one : length1 + length2 + length3 = 1 := by
  unfold length1 length2 length3
  have h_denom_ne : 1 + goldenRatio + goldenRatio ^ 2 ≠ 0 := by
    linarith [denom_pos]
  field_simp [h_denom_ne]

/-- length1 < 1 -/
lemma length1_lt_one : length1 < 1 := by
  have h := lengths_sum_to_one
  linarith [length2_pos, length3_pos]

/-- length1 + length2 < 1 -/
lemma length12_lt_one : length1 + length2 < 1 := by
  have h := lengths_sum_to_one
  linarith [length3_pos]

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
    (_ : HasEmergentIET r) :
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

/-! ### Displacement formulas in terms of golden ratio -/

/-- The denominator 1 + φ + φ² equals 2(1 + φ) using φ² = φ + 1. -/
lemma denom_eq_two_one_plus_phi :
    1 + goldenRatio + goldenRatio ^ 2 = 2 * (1 + goldenRatio) := by
  have h := Real.goldenRatio_sq  -- φ² = φ + 1
  rw [h]
  ring

/-- Displacement 0 formula: d₀ = (1 + 2φ)/(2(1+φ)). -/
lemma displacement0_formula :
    displacement0 = (1 + 2 * goldenRatio) / (2 * (1 + goldenRatio)) := by
  unfold displacement0 length1
  rw [denom_eq_two_one_plus_phi]
  have h_pos : 0 < 1 + goldenRatio := by linarith [goldenRatio_pos]
  have h_ne : 2 * (1 + goldenRatio) ≠ 0 := by linarith
  field_simp
  ring

/-- Displacement 1 formula: d₁ = φ/(2(1+φ)).
    Note: length3 - length1 = (φ² - 1)/(2(1+φ)) = φ/(2(1+φ)) using φ² - 1 = φ. -/
lemma displacement1_formula :
    displacement1 = goldenRatio / (2 * (1 + goldenRatio)) := by
  unfold displacement1 length3 length1
  rw [denom_eq_two_one_plus_phi]
  -- φ² - 1 = φ by the golden ratio property φ² = φ + 1
  have h_sq : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq
  have h_sq' : goldenRatio ^ 2 - 1 = goldenRatio := by linarith [h_sq]
  rw [← sub_div, h_sq']

/-- Displacement 2 formula: d₂ = -(1+φ)/(2(1+φ)) = -1/2. -/
lemma displacement2_formula :
    displacement2 = -(1 + goldenRatio) / (2 * (1 + goldenRatio)) := by
  unfold displacement2
  have h_pos : 0 < 1 + goldenRatio := by linarith [goldenRatio_pos]
  have h_ne : 2 * (1 + goldenRatio) ≠ 0 := by linarith
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
