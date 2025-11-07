/-
Copyright (c) 2025-11-06. All rights reserved.
Released under Apache 2.0 license.

Helper lemmas for golden ratio identities needed for norm bound proofs
in the TDCSG project.

CORRECTED VERSION - fixes notation issues with ψ
-/
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Golden Ratio Helper Identities

This file contains key identities involving the golden ratio φ,
along with trigonometric relations needed for the GG(5,5) norm bound proofs.

## Main definitions and lemmas

From Mathlib:
- `goldenRatio`: φ = (1 + √5)/2
- `goldenConj`: ψ_neg = (1 - √5)/2 (NEGATIVE!)
- `goldenRatio_sq`: φ² = φ + 1
- `goldenConj_sq`: ψ_neg² = ψ_neg + 1
- `goldenRatio_add_goldenConj`: φ + ψ_neg = 1
- `goldenRatio_mul_goldenConj`: φ * ψ_neg = -1
- `cos_pi_div_five`: cos(π/5) = (1 + √5)/4 = φ/2

Custom lemmas:
- Relations between φ and √5
- cos(2π/5) = (φ-1)/2
- sin²(2π/5) identities
- r_crit² = 3 + φ relations

IMPORTANT NOTE: The positive golden conjugate psi = (√5-1)/2 = φ - 1
is DIFFERENT from Mathlib's goldenConj = (1-√5)/2 which is negative.
-/

namespace GoldenRatioHelpers

open Real

-- Notation for golden ratio
local notation "φ" => Real.goldenRatio

/-- The positive golden conjugate: (√5-1)/2 = φ - 1.
    This is the POSITIVE value, unlike Mathlib's goldenConj which is negative. -/
noncomputable def psi : ℝ := (√5 - 1) / 2

/-- φ - 1 = 1/φ -/
lemma phi_sub_one : φ - 1 = 1 / φ := by
  have h : φ^2 = φ + 1 := goldenRatio_sq
  have hne : φ ≠ 0 := goldenRatio_ne_zero
  rw [eq_div_iff hne]
  calc (φ - 1) * φ = φ * φ - φ := by ring
    _ = φ^2 - φ := by ring
    _ = (φ + 1) - φ := by rw [h]
    _ = 1 := by ring

/-- 2φ - 1 = √5 -/
lemma two_phi_sub_one : 2 * φ - 1 = √5 := by
  unfold goldenRatio
  field_simp
  ring

/-- φ - Mathlib's goldenConj = √5 -/
lemma phi_sub_goldenConj : φ - goldenConj = √5 := by
  unfold goldenRatio goldenConj
  field_simp
  ring

/-- The positive psi equals φ - 1 -/
lemma psi_eq_phi_sub_one : psi = φ - 1 := by
  unfold psi goldenRatio
  field_simp
  ring

/-- psi = 1 / φ -/
lemma psi_eq_one_div_phi : psi = 1 / φ := by
  rw [psi_eq_phi_sub_one, phi_sub_one]

/-- Mathlib's goldenConj = -(φ - 1) = 1 - φ -/
lemma goldenConj_eq_one_sub_phi : goldenConj = 1 - φ := by
  have h : φ + goldenConj = 1 := goldenRatio_add_goldenConj
  linarith

/-- Mathlib's goldenConj = -psi -/
lemma goldenConj_eq_neg_psi : goldenConj = -psi := by
  rw [psi_eq_phi_sub_one, goldenConj_eq_one_sub_phi]
  ring

/-- cos(π/5) = φ/2 -/
lemma cos_pi_div_five_eq_phi_div_two : cos (π / 5) = φ / 2 := by
  rw [cos_pi_div_five]
  unfold goldenRatio
  ring

/-- cos(2π/5) = (φ - 1) / 2 = psi / 2 -/
lemma cos_two_pi_div_five : cos (2 * π / 5) = (φ - 1) / 2 := by
  -- Use the double angle formula: cos(2θ) = 2cos²(θ) - 1
  have eq_form : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [eq_form]
  have double_angle : cos (2 * (π / 5)) = 2 * cos (π / 5)^2 - 1 := cos_two_mul (π / 5)
  rw [double_angle, cos_pi_div_five_eq_phi_div_two]
  -- Now we have: 2 * (φ/2)² - 1 = (φ-1)/2
  -- LHS = 2 * φ²/4 - 1 = φ²/2 - 1
  -- We know φ² = φ + 1, so φ²/2 - 1 = (φ+1)/2 - 1 = (φ-1)/2
  have h : φ^2 = φ + 1 := goldenRatio_sq
  have step1 : 2 * (φ / 2) ^ 2 - 1 = 2 * (φ^2 / 4) - 1 := by ring
  have step2 : 2 * (φ^2 / 4) - 1 = φ^2 / 2 - 1 := by ring
  have step3 : φ^2 / 2 - 1 = (φ + 1) / 2 - 1 := by rw [h]
  have step4 : (φ + 1) / 2 - 1 = (φ - 1) / 2 := by ring
  rw [step1, step2, step3, step4]

/-- Alternative form: cos(2π/5) = psi/2 -/
lemma cos_two_pi_div_five_psi : cos (2 * π / 5) = psi / 2 := by
  rw [cos_two_pi_div_five, psi_eq_phi_sub_one]

/-- Alternative form: cos(2π/5) = (√5 - 1) / 4 -/
lemma cos_two_pi_div_five_sqrt : cos (2 * π / 5) = (√5 - 1) / 4 := by
  rw [cos_two_pi_div_five]
  unfold goldenRatio
  field_simp
  ring

/-- sin²(π/5) in terms of φ -/
lemma sin_sq_pi_div_five : sin (π / 5)^2 = (3 - φ) / 4 := by
  have pyth : sin (π / 5)^2 + cos (π / 5)^2 = 1 := sin_sq_add_cos_sq (π / 5)
  have cos_val : cos (π / 5) = φ / 2 := cos_pi_div_five_eq_phi_div_two
  have h : φ^2 = φ + 1 := goldenRatio_sq
  calc sin (π / 5)^2
      = 1 - cos (π / 5)^2 := by
        have : cos (π / 5)^2 = 1 - sin (π / 5)^2 := by linarith [pyth]
        linarith
    _ = 1 - (φ / 2)^2 := by rw [cos_val]
    _ = 1 - φ^2 / 4 := by ring
    _ = (4 - φ^2) / 4 := by ring
    _ = (4 - (φ + 1)) / 4 := by rw [h]
    _ = (3 - φ) / 4 := by ring

/-- sin²(2π/5) = (5 + √5) / 8 (corrected from original which had minus sign) -/
lemma sin_sq_two_pi_div_five : sin (2 * π / 5)^2 = (5 + √5) / 8 := by
  have pyth : sin (2 * π / 5)^2 + cos (2 * π / 5)^2 = 1 :=
    sin_sq_add_cos_sq (2 * π / 5)
  have cos_val : cos (2 * π / 5) = (√5 - 1) / 4 := cos_two_pi_div_five_sqrt
  -- cos²(2π/5) = ((√5-1)/4)² = (√5-1)²/16 = (6-2√5)/16 = (3-√5)/8
  have sqrt5_sq : (√(5:ℝ))^2 = 5 := sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have cos_sq : ((√5 - 1) / 4)^2 = (3 - √5) / 8 := by
    calc ((√5 - 1) / 4)^2
        = (√5 - 1)^2 / 16 := by ring
      _ = ((√5)^2 - 2*√5 + 1) / 16 := by ring
      _ = (5 - 2*√5 + 1) / 16 := by rw [sqrt5_sq]
      _ = (6 - 2*√5) / 16 := by ring
      _ = (3 - √5) / 8 := by ring
  -- sin²(2π/5) = 1 - cos²(2π/5) = 1 - (3-√5)/8 = (5+√5)/8
  calc sin (2 * π / 5)^2
      = 1 - cos (2 * π / 5)^2 := by
        have step : cos (2 * π / 5)^2 + sin (2 * π / 5)^2 = 1 := by linarith [pyth]
        linarith [step]
    _ = 1 - ((√5 - 1) / 4)^2 := by rw [cos_val]
    _ = 1 - (3 - √5) / 8 := by rw [cos_sq]
    _ = (8 - (3 - √5)) / 8 := by ring
    _ = (5 + √5) / 8 := by ring

/-- r_crit² = 3 + φ = 4 + goldenConj -/
lemma r_crit_sq_alt : 3 + φ = 4 + goldenConj := by
  have h : goldenConj = 1 - φ := goldenConj_eq_one_sub_phi
  linarith

/-- For polyrith: φ² - φ - 1 = 0 -/
lemma phi_polynomial : φ^2 - φ - 1 = 0 := by
  have h : φ^2 = φ + 1 := goldenRatio_sq
  linarith

/-- φ is approximately 1.618 (useful for numerical verification) -/
lemma phi_bounds : 1 < φ ∧ φ < 2 := by
  constructor
  · have h : φ^2 = φ + 1 := goldenRatio_sq
    have hp : 0 < φ := goldenRatio_pos
    nlinarith [sq_nonneg (φ - 1), h]
  · exact goldenRatio_lt_two

/-- √5 bounds -/
lemma sqrt_five_bounds : 2 < √5 ∧ √5 < 3 := by
  constructor
  · have : (2:ℝ)^2 < 5 := by norm_num
    calc 2 = √(2^2) := by simp; norm_num
      _ < √5 := sqrt_lt_sqrt (by norm_num) this
  · have : (5:ℝ) < 3^2 := by norm_num
    calc √5 < √(3^2) := sqrt_lt_sqrt (by norm_num) this
      _ = 3 := by simp; norm_num

/-- φ - 1 is positive -/
lemma phi_sub_one_pos : 0 < φ - 1 := by
  have h : 1 < φ := phi_bounds.1
  linarith

/-- psi is positive -/
lemma psi_pos : 0 < psi := by
  rw [psi_eq_phi_sub_one]
  exact phi_sub_one_pos

/-- Useful for nlinarith: (3 + φ) is positive -/
lemma three_plus_phi_pos : 0 < 3 + φ := by
  linarith [goldenRatio_pos]

/-- (3 + φ)² expanded -/
lemma three_plus_phi_sq : (3 + φ)^2 = 13 + 6 * φ := by
  have h : φ^2 = φ + 1 := goldenRatio_sq
  calc (3 + φ)^2 = 9 + 6 * φ + φ^2 := by ring_nf
    _ = 9 + 6 * φ + (φ + 1) := by rw [h]
    _ = 13 + 6 * φ := by ring_nf

end GoldenRatioHelpers
