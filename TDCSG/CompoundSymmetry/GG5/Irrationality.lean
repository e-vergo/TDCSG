/-
Copyright (c) 2025 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.CompoundSymmetry.GG5.IET
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrationality and Golden Ratio Properties for GG5

This file establishes irrationality results related to the golden ratio
that are used in proving the GG5 interval exchange transformation has
infinite orbits.

## Main results

* `goldenRatio_mul_rat_irrational`: Golden ratio times any nonzero rational is irrational
* `GG5_IET_rotation_irrational`: The GG5 IET rotation ratio length2/length1 = φ is irrational
* `int_add_int_mul_phi_eq_zero`: Linear independence of {1, φ} over ℤ
* `denom_eq_two_one_plus_phi`: 1 + φ + φ² = 2(1 + φ)
* `interval2_image_bound`: length1 + length2 = 1/2
* `length3_gt_length1`, `length1_lt_half`: Key inequalities for interval lengths
-/

namespace CompoundSymmetry.GG5

open Real

/-! ### Irrationality results -/

/-- The golden ratio times any nonzero rational is irrational. -/
theorem goldenRatio_mul_rat_irrational (q : ℚ) (hq : q ≠ 0) :
    Irrational (goldenRatio * q) := by
  intro ⟨r, hr⟩
  have h_phi_irr := goldenRatio_irrational
  apply h_phi_irr
  use r / q
  have hq_cast : (q : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hq
  rw [Rat.cast_div, div_eq_iff hq_cast, ← hr]

/-- The GG5 IET rotation ratio is irrational.
    Since length2 = φ * length1, we have length2/length1 = φ. -/
theorem GG5_IET_rotation_irrational :
    Irrational (length2 / length1) := by
  have h_rel := interval_lengths_golden_ratio_relations.1
  rw [h_rel]
  have h1_pos := length1_pos
  have h1_ne : length1 ≠ 0 := ne_of_gt h1_pos
  rw [mul_div_assoc, div_self h1_ne, mul_one]
  exact goldenRatio_irrational

/-! ### Denominator properties -/

/-- The denominator 1 + φ + φ² is positive. -/
theorem denom_pos : 0 < 1 + goldenRatio + goldenRatio ^ 2 := by
  have h1 : 0 < goldenRatio := goldenRatio_pos
  have h2 : 0 < goldenRatio ^ 2 := sq_pos_of_pos h1
  linarith

/-- If a + b*φ = 0 for integers a, b, then a = b = 0.
    This is the linear independence of {1, φ} over ℤ. -/
theorem int_add_int_mul_phi_eq_zero (a b : ℤ)
    (h : (a : ℝ) + (b : ℝ) * goldenRatio = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · -- If b = 0, then a = 0 follows from h
    simp only [hb, Int.cast_zero, zero_mul, add_zero] at h
    have ha : a = 0 := by
      have : (a : ℝ) = 0 := h
      exact Int.cast_eq_zero.mp this
    exact ⟨ha, hb⟩
  · -- If b ≠ 0, derive contradiction from irrationality
    exfalso
    have hφ : goldenRatio = -(a : ℝ) / b := by
      have hb_ne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
      field_simp at h ⊢
      linarith
    -- goldenRatio equals a rational, contradicting irrationality
    have : Irrational goldenRatio := goldenRatio_irrational
    apply this
    use ((-a : ℤ) : ℚ) / b
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    push_cast
    exact hφ.symm

/-- The denominator 1 + φ + φ² equals 2(1 + φ) using φ² = φ + 1. -/
theorem denom_eq_two_one_plus_phi :
    1 + goldenRatio + goldenRatio ^ 2 = 2 * (1 + goldenRatio) := by
  have h := Real.goldenRatio_sq  -- φ² = φ + 1
  rw [h]
  ring

/-- length1 = 1 / (2 * (1 + φ)) -/
theorem length1_alt : length1 = 1 / (2 * (1 + goldenRatio)) := by
  unfold length1
  rw [denom_eq_two_one_plus_phi]

/-! ### Interval length properties -/

/-- Interval 2 maps to [0, 0.5) under GG5 IET.
    More precisely, interval 2 = [length1 + length2, 1) maps to [0, length3).
    Since length3 = φ² * length1 and length1 + length2 = (1+φ) * length1,
    the image spans half the unit interval. -/
theorem interval2_image_bound :
    length1 + length2 = 1 / 2 := by
  have h := denom_eq_two_one_plus_phi
  unfold length1 length2
  rw [h]
  field_simp

/-- Key inequality: length3 > length1 (equivalently φ² > 1) -/
theorem length3_gt_length1 : length3 > length1 := by
  unfold length1 length3
  have hφ_gt1 : goldenRatio > 1 := Real.one_lt_goldenRatio
  have hφ_pos : goldenRatio > 0 := Real.goldenRatio_pos
  have hφ2_gt1 : goldenRatio ^ 2 > 1 := by nlinarith
  have h_denom_pos : 1 + goldenRatio + goldenRatio ^ 2 > 0 := denom_pos
  apply div_lt_div_of_pos_right _ h_denom_pos
  linarith

/-- Key inequality: length1 < 1/2 -/
theorem length1_lt_half : length1 < 1 / 2 := by
  have hφ := goldenRatio_pos
  have hφ2 : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq
  have h_denom : 1 + goldenRatio + goldenRatio ^ 2 = 2 + 2 * goldenRatio := by
    rw [hφ2]; ring
  have h_denom_pos : (0 : ℝ) < 2 + 2 * goldenRatio := by linarith
  unfold length1
  rw [h_denom]
  rw [one_div_lt_one_div h_denom_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- 2 * (1 + φ) is positive -/
theorem two_one_plus_phi_pos : (0 : ℝ) < 2 * (1 + goldenRatio) := by
  have hφ := goldenRatio_pos
  linarith

end CompoundSymmetry.GG5
