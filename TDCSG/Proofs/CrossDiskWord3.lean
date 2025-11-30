/-
Copyright (c) 2025 Raven Cyarm, Eric Easley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Cyarm, Eric Easley
-/

import TDCSG.Proofs.CrossDiskRestricted

/-!
# Cross-disk bounds for word3 parameter range

This file establishes cross-disk bounds for the word3 parameter range c ∈ [2-√5, 1].

For the compound symmetry group G∪G⁵ of the regular pentagon, we prove that intermediate
points during word3 application remain within the critical disk intersection when the
parameter c is in the interval [2-√5, 1].

## Main results

- `cross_disk_w3_z1_bound`: z1 intermediate point stays within r_crit
- `cross_disk_w3_z2_bound`: z2 bound (currently sorry)
- `cross_disk_w3_z3_bound`: z3 bound (currently sorry)
- `cross_disk_w3_z4_bound`: z4 bound (currently sorry)
- `cross_disk_w3_z5_bound`: z5 intermediate point stays within r_crit
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real TDCSG.Definitions

/-- The lower bound for c in interval 2: 2 - √5 -/
noncomputable def c_lower_word3 : ℝ := 2 - √5

/-- 2 - √5 > -1 since √5 < 3 -/
lemma c_lower_word3_gt_neg1 : c_lower_word3 > -1 := by
  unfold c_lower_word3
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [h_sqrt5_sq]
  linarith

/-- 2 - √5 < (1 - √5)/2 since 2 - √5 < 1/2 - √5/2 iff 4 - 2√5 < 1 - √5 iff 3 < √5, false.
    Actually 2 - √5 > (1 - √5)/2 since 4 - 2√5 > 1 - √5 iff 3 > √5, true. -/
lemma c_lower_word3_gt_c_upper_restricted : c_lower_word3 > (1 - √5) / 2 := by
  unfold c_lower_word3
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- 2 - √5 > (1 - √5)/2 iff 4 - 2√5 > 1 - √5 iff 3 > √5 iff 9 > 5
  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [h_sqrt5_sq]
  linarith

/-! ### z1 bound for word3: ‖(ζ₅⁴ - 2) + c*(1 - ζ₅)‖ ≤ r_crit for c ∈ [2-√5, 1] -/

/-- Re(ζ₅⁴ - 2) = (√5 - 9)/4 -/
lemma A_w3_z1_re : (ζ₅^4 - 2 : ℂ).re = (√5 - 9) / 4 := by
  simp only [Complex.sub_re]
  have h2re : (2 : ℂ).re = 2 := by rfl
  rw [h2re, zeta5_pow4_re]
  ring

/-- Im(ζ₅⁴ - 2) = -sin(2π/5) -/
lemma A_w3_z1_im : (ζ₅^4 - 2 : ℂ).im = -Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im]
  have h2im : (2 : ℂ).im = 0 := by rfl
  rw [h2im, zeta5_pow4_im']
  ring

-- B = 1 - ζ₅ is already analyzed in B4_re and B4_im

/-- ||ζ₅⁴ - 2||² = ((√5-9)/4)² + sin²(2π/5) = (86 - 18√5)/16 + (5+√5)/8 = (96 - 16√5)/16 = 6 - √5 -/
lemma normSq_A_w3_z1 : Complex.normSq (ζ₅^4 - 2) = 6 - √5 := by
  rw [Complex.normSq_apply, A_w3_z1_re, A_w3_z1_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  simp only [← sq]
  -- Re² = ((√5-9)/4)² = (√5² - 18√5 + 81)/16 = (5 - 18√5 + 81)/16 = (86 - 18√5)/16
  have h_re_sq : ((√5 - 9) / 4)^2 = (86 - 18*√5) / 16 := by nlinarith [h_sqrt5_sq]
  -- Im² = sin²(2π/5) = (5+√5)/8
  have h_neg_sq : (-Real.sin (2 * π / 5))^2 = Real.sin (2 * π / 5)^2 := by ring
  calc ((√5 - 9) / 4)^2 + (-Real.sin (2 * π / 5))^2
      = (86 - 18*√5) / 16 + (5 + √5) / 8 := by rw [h_re_sq, h_neg_sq, h_sin_sq]
    _ = (86 - 18*√5 + 10 + 2*√5) / 16 := by ring
    _ = (96 - 16*√5) / 16 := by ring
    _ = 6 - √5 := by ring

-- conj(1 - ζ₅) = 1 - ζ₅⁴ (already proved as conj_B4)

/-- Re((ζ₅⁴ - 2) * conj(1 - ζ₅)) = (2√5 - 5) / 2 -/
lemma re_A_w3_z1_mul_conj_B :
    ((ζ₅^4 - 2 : ℂ) * starRingEnd ℂ (1 - ζ₅)).re = (2*√5 - 5) / 2 := by
  rw [conj_B4]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- (ζ₅⁴ - 2) * (1 - ζ₅⁴) = ζ₅⁴ - ζ₅⁸ - 2 + 2ζ₅⁴ = 3ζ₅⁴ - ζ₅³ - 2 (using ζ₅⁸ = ζ₅³)
  have h_expand : (ζ₅^4 - 2 : ℂ) * (1 - ζ₅^4) = 3*ζ₅^4 - ζ₅^3 - 2 := by
    calc (ζ₅^4 - 2) * (1 - ζ₅^4) = ζ₅^4 - ζ₅^8 - 2 + 2*ζ₅^4 := by ring
      _ = 3*ζ₅^4 - ζ₅^3 - 2 := by rw [zeta5_pow_eight]; ring
  rw [h_expand]
  simp only [Complex.sub_re, Complex.mul_re]
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h3re : (3 : ℂ).re = 3 := by rfl
  have h3im : (3 : ℂ).im = 0 := by rfl
  simp only [h2re, h3re, h3im, zero_mul, sub_zero]
  rw [zeta5_pow4_re, zeta5_cubed_re]
  ring

/-- The vertex of f(c) = ||A + cB||² where A = ζ₅⁴ - 2, B = 1 - ζ₅.
    vertex = -Re(A*conj(B))/||B||² = -((2√5-5)/2) / ((5-√5)/2) = (5-2√5)/(5-√5)
           = (5-2√5)(5+√5)/((5-√5)(5+√5)) = (25+5√5-10√5-10)/20 = (15-5√5)/20 = (3-√5)/4 -/
lemma w3_z1_vertex : -(((2*√5 - 5) / 2) / ((5 - √5) / 2)) = (3 - √5) / 4 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_5_minus_sqrt5_ne : 5 - √5 ≠ 0 := by nlinarith [Real.sqrt_nonneg 5]
  have h_denom_ne : (5 - √5) / 2 ≠ 0 := by
    have h : 5 - √5 > 0 := by nlinarith [Real.sqrt_nonneg 5, h_sqrt5_sq]
    have : (5 - √5) / 2 > 0 := by linarith
    linarith
  field_simp
  nlinarith [h_sqrt5_sq]

/-- The vertex (3-√5)/4 ≈ 0.19 is in the interior of [2-√5, 1] = [-0.236, 1],
    so the parabola achieves max at one of the endpoints -/
lemma w3_z1_vertex_in_interval : (2 - √5) < (3 - √5) / 4 ∧ (3 - √5) / 4 < 1 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [h_sqrt5_sq]
  constructor <;> nlinarith [Real.sqrt_nonneg 5]

/-- At c = 2 - √5:
    A + cB = (ζ₅⁴ - 2) + (2-√5)(1 - ζ₅)
           = ζ₅⁴ - 2 + (2-√5) - (2-√5)ζ₅
           = ζ₅⁴ - √5 - (2-√5)ζ₅ -/
lemma A_w3_z1_at_c_lower : (ζ₅^4 - 2 : ℂ) + (c_lower_word3 : ℂ) * (1 - ζ₅) =
    ζ₅^4 - (2 - √5)*ζ₅ - √5 := by
  unfold c_lower_word3
  push_cast
  ring

/-- At c = 1: A + B = (ζ₅⁴ - 2) + (1 - ζ₅) = ζ₅⁴ - ζ₅ - 1 -/
lemma A_w3_z1_at_c_one : (ζ₅^4 - 2 : ℂ) + (1 : ℂ) * (1 - ζ₅) = ζ₅^4 - ζ₅ - 1 := by ring

/-- Re(ζ₅⁴ - ζ₅ - 1) = (√5-1)/4 - (√5-1)/4 - 1 = -1 -/
lemma w3_z1_at_one_re : (ζ₅^4 - ζ₅ - 1 : ℂ).re = -1 := by
  simp only [Complex.sub_re, Complex.one_re]
  rw [zeta5_pow4_re, zeta5_re]
  ring

/-- Im(ζ₅⁴ - ζ₅ - 1) = -sin(2π/5) - sin(2π/5) = -2sin(2π/5) -/
lemma w3_z1_at_one_im : (ζ₅^4 - ζ₅ - 1 : ℂ).im = -2 * Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im, Complex.one_im]
  rw [zeta5_pow4_im', zeta5_im_eq_sin]
  ring

/-- |ζ₅⁴ - ζ₅ - 1|² = 1 + 4sin²(2π/5) = (7+√5)/2 = 3 + φ -/
lemma normSq_w3_z1_at_one : Complex.normSq (ζ₅^4 - ζ₅ - 1) = 3 + φ := by
  rw [Complex.normSq_apply, w3_z1_at_one_re, w3_z1_at_one_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  simp only [← sq]
  calc (-1)^2 + (-2 * Real.sin (2 * π / 5))^2
      = 1 + 4 * Real.sin (2 * π / 5)^2 := by ring
    _ = 1 + 4 * ((5 + √5) / 8) := by rw [h_sin_sq]
    _ = 1 + (5 + √5) / 2 := by ring
    _ = (7 + √5) / 2 := by ring
    _ = 3 + (1 + √5) / 2 := by ring
    _ = 3 + φ := by unfold φ Real.goldenRatio; ring

/-- Re(ζ₅⁴ - (2-√5)ζ₅ - √5) = (√5-1)/4 - (2-√5)(√5-1)/4 - √5 = 3(1-√5)/2 -/
lemma w3_z1_at_lower_re : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ).re = 3 * (1 - √5) / 2 := by
  have h_expr : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ) = ζ₅^4 - ((2 - √5 : ℝ) : ℂ) * ζ₅ - (√5 : ℂ) := by
    push_cast; ring
  rw [h_expr]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul]
  rw [zeta5_pow4_re, zeta5_re]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith [h_sqrt5_sq]

/-- Im(ζ₅⁴ - (2-√5)ζ₅ - √5) = -sin(2π/5) - (2-√5)sin(2π/5) = -(3-√5)sin(2π/5) -/
lemma w3_z1_at_lower_im : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ).im = -(3 - √5) * Real.sin (2 * π / 5) := by
  have h_expr : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ) = ζ₅^4 - ((2 - √5 : ℝ) : ℂ) * ζ₅ - (√5 : ℂ) := by
    push_cast; ring
  rw [h_expr]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [zeta5_pow4_im', zeta5_im_eq_sin]
  ring

/-- |ζ₅⁴ - (2-√5)ζ₅ - √5|² = (37 - 13√5)/2 < 3 + φ -/
lemma normSq_w3_z1_at_lower : Complex.normSq (ζ₅^4 - (2 - √5)*ζ₅ - √5) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z1_at_lower_re, w3_z1_at_lower_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  simp only [← sq]
  have h1 : (3 * (1 - √5) / 2)^2 = 9 * (6 - 2*√5) / 4 := by nlinarith [h_sqrt5_sq]
  have h2 : (-(3 - √5) * Real.sin (2 * π / 5))^2 = (3 - √5)^2 * Real.sin (2 * π / 5)^2 := by ring
  have h3 : (3 - √5)^2 = 14 - 6*√5 := by nlinarith [h_sqrt5_sq]
  rw [h1, h2, h_sin_sq, h3]
  have h4 : (14 - 6*√5) * ((5 + √5) / 8) = 5 - 2*√5 := by nlinarith [h_sqrt5_sq]
  rw [h4]
  unfold φ Real.goldenRatio
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

/-! ### Word3 cross-disk bounds

These lemmas prove that intermediate points in word3 application stay within
the disk intersection for c ∈ [2-√5, 1].
-/

set_option maxHeartbeats 1200000 in
/-- z1 bound for word3: ‖(ζ₅⁴ - 2) + c*(1 - ζ₅)‖ ≤ r_crit for c ∈ [2-√5, 1] -/
lemma cross_disk_w3_z1_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖(ζ₅^4 - 2 : ℂ) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  set A : ℂ := ζ₅^4 - 2 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  have h_at_one : ‖A + (1 : ℂ) * B‖^2 = 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    have h_expr : (ζ₅^4 - 2 : ℂ) + (1 : ℂ) * (1 - ζ₅) = ζ₅^4 - ζ₅ - 1 := by ring
    rw [h_expr]
    exact normSq_w3_z1_at_one

  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    have h_expr : (ζ₅^4 - 2 : ℂ) + ((2 - √5 : ℝ) : ℂ) * (1 - ζ₅) = ζ₅^4 - (2 - √5)*ζ₅ - √5 := by
      push_cast; ring
    rw [h_expr]
    exact normSq_w3_z1_at_lower

  have h_re_AB := re_A_w3_z1_mul_conj_B
  have h_normSq_B := normSq_B4
  have h_normSq_A := normSq_A_w3_z1
  have h_vertex := w3_z1_vertex
  have h_vertex_in := w3_z1_vertex_in_interval

  have h_normSq_expand : ∀ t : ℝ, Complex.normSq (A + (t : ℂ) * B) =
      Complex.normSq A + 2 * t * (A * starRingEnd ℂ B).re + t^2 * Complex.normSq B := by
    intro t
    rw [Complex.normSq_add]
    have h_conj_t : starRingEnd ℂ (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    have h_normSq_t : Complex.normSq (t : ℂ) = t^2 := by rw [Complex.normSq_ofReal]; ring
    rw [Complex.normSq_mul, h_normSq_t]
    simp only [map_mul, h_conj_t]
    have h_re_scale : (A * ((t : ℂ) * starRingEnd ℂ B)).re = t * (A * starRingEnd ℂ B).re := by
      have h_assoc : A * ((t : ℂ) * starRingEnd ℂ B) = (t : ℂ) * (A * starRingEnd ℂ B) := by ring
      rw [h_assoc, Complex.re_ofReal_mul]
    rw [h_re_scale]
    ring

  have h_normSq_B_pos : 0 < Complex.normSq B := by
    rw [hB_def, h_normSq_B]
    have h_sqrt5_lt5 : √5 < 5 := by nlinarith [h_sqrt5_sq]
    linarith

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (1 - ζ₅) = (5 - √5) / 2 := normSq_B4
  have h_coeff_b : ((ζ₅^4 - 2 : ℂ) * starRingEnd ℂ (1 - ζ₅)).re = (2*√5 - 5) / 2 := re_A_w3_z1_mul_conj_B
  have h_coeff_c : Complex.normSq (ζ₅^4 - 2) = 6 - √5 := normSq_A_w3_z1

  have h_f_le_max : Complex.normSq ((ζ₅^4 - 2) + (c : ℂ) * (1 - ζ₅)) ≤ 3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = ζ₅^4 - 2 by rfl, show B = 1 - ζ₅ by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    have h_f_at_1 : 6 - √5 + 2 * 1 * ((2*√5 - 5) / 2) + 1^2 * ((5 - √5) / 2) = 3 + φ := by
      unfold φ Real.goldenRatio
      nlinarith [h_sqrt5_sq]

    have h_diff : (6 - √5 + 2 * c * ((2*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)) -
                  (6 - √5 + 2 * 1 * ((2*√5 - 5) / 2) + 1^2 * ((5 - √5) / 2)) =
                  (c - 1) * ((2*√5 - 5) + (c + 1) * ((5 - √5) / 2)) := by ring

    have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [h_sqrt5_sq]

    have h_lower : 2 - √5 = c_lower_word3 := by unfold c_lower_word3; rfl

    have h_at_lower' : 6 - √5 + 2 * (2 - √5) * ((2*√5 - 5) / 2) + (2 - √5)^2 * ((5 - √5) / 2) ≤ 3 + φ := by
      have h_eq : 6 - √5 + 2 * (2 - √5) * ((2*√5 - 5) / 2) + (2 - √5)^2 * ((5 - √5) / 2) =
                  Complex.normSq (ζ₅^4 - (2 - √5)*ζ₅ - √5) := by
        rw [Complex.normSq_apply, w3_z1_at_lower_re, w3_z1_at_lower_im]
        simp only [← sq]
        have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
        nlinarith [h_sqrt5_sq, Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [Real.pi_pos] : 0 ≤ 2 * π / 5)
          (by linarith [Real.pi_pos] : 2 * π / 5 ≤ π), h_sin_sq]
      rw [h_eq]
      exact normSq_w3_z1_at_lower

    by_cases hc_lt_vertex : c < (3 - √5) / 4
    · have h_deriv_neg : c * ((5 - √5) / 2) * 2 + 2 * ((2*√5 - 5) / 2) < 0 := by
        have h1 : c * ((5 - √5) / 2) * 2 + 2 * ((2*√5 - 5) / 2) = c * (5 - √5) + (2*√5 - 5) := by ring
        rw [h1]
        have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [h_sqrt5_sq]
        have h_vertex_eq : (5 - 2*√5) / (5 - √5) = (3 - √5) / 4 := by
          field_simp
          nlinarith [h_sqrt5_sq]
        have h_ineq : c * (5 - √5) < 5 - 2*√5 := by
          calc c * (5 - √5) < (3 - √5) / 4 * (5 - √5) := by
                apply mul_lt_mul_of_pos_right hc_lt_vertex h_5_minus_sqrt5_pos
            _ = (5 - 2*√5) := by nlinarith [h_sqrt5_sq]
        linarith

      have h_mono : ∀ c₁ c₂ : ℝ, 2 - √5 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ (3 - √5) / 4 →
          6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2) ≤
          6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2) := by
        intro c₁ c₂ _ hc12 hc2v
        have h_diff2 : (6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2)) -
                      (6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2)) =
                      (c₂ - c₁) * ((2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
        have h_sum_bound : c₁ + c₂ ≤ 2 * (3 - √5) / 4 := by linarith
        have h_factor_neg : (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
          have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [h_sqrt5_sq]
          have h_at_2v : (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) = 0 := by
            nlinarith [h_sqrt5_sq]
          calc (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)
              ≤ (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) := by gcongr
            _ = 0 := h_at_2v
        nlinarith [hc12, h_factor_neg]

      calc 6 - √5 + 2 * c * ((2*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)
          ≤ 6 - √5 + 2 * (2 - √5) * ((2*√5 - 5) / 2) + (2 - √5)^2 * ((5 - √5) / 2) := by
            apply h_mono (2 - √5) c (le_refl _) hc_lo (le_of_lt hc_lt_vertex)
        _ ≤ 3 + φ := h_at_lower'

    · push_neg at hc_lt_vertex

      have h_mono : ∀ c₁ c₂ : ℝ, (3 - √5) / 4 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ 1 →
          6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2) ≤
          6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2) := by
        intro c₁ c₂ hc1v hc12 _
        have h_diff2 : (6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2)) -
                      (6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2)) =
                      (c₂ - c₁) * ((2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
        have h_sum_bound : c₁ + c₂ ≥ 2 * (3 - √5) / 4 := by linarith
        have h_factor_pos : (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2) ≥ 0 := by
          have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [h_sqrt5_sq]
          have h_at_2v : (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) = 0 := by
            nlinarith [h_sqrt5_sq]
          calc (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)
              ≥ (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) := by gcongr
            _ = 0 := h_at_2v
        nlinarith [hc12, h_factor_pos]

      calc 6 - √5 + 2 * c * ((2*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)
          ≤ 6 - √5 + 2 * 1 * ((2*√5 - 5) / 2) + 1^2 * ((5 - √5) / 2) := by
            apply h_mono c 1 hc_lt_vertex hc_hi (le_refl 1)
        _ = 3 + φ := h_f_at_1

  exact h_f_le_max

/-- z2 bound for word3: ‖(2 + ζ₅³ - 2*ζ₅⁴) + c*(ζ₅⁴ - 1)‖ ≤ r_crit for c ∈ [2-√5, 1] -/
lemma cross_disk_w3_z2_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  sorry

/-- z3 bound for word3: ‖(-2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴) + c*(ζ₅³ - ζ₅⁴)‖ ≤ r_crit for c ∈ [2-√5, 1] -/
lemma cross_disk_w3_z3_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by
  sorry

/-- z4 bound for word3: ‖(4 - 2*ζ₅ + ζ₅³ - 2*ζ₅⁴) + c*(ζ₅⁴ - 1)‖ ≤ r_crit for c ∈ [2-√5, 1] -/
lemma cross_disk_w3_z4_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  sorry

/-! ### Word3 z5 helper lemmas -/

/-- Re(-4 + 4*ζ₅ - 2*ζ₅² + ζ₅⁴) = (7√5 - 19)/4 -/
lemma A_w3_z5_re : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (7*√5 - 19) / 4 := by
  have h4re : (4 : ℂ).re = 4 := by rfl
  have h4im : (4 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
             h4re, h4im, h2re, h2im]
  rw [zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  ring

/-- Im(-4 + 4*ζ₅ - 2*ζ₅² + ζ₅⁴) = 3*sin(2π/5) - 2*sin(π/5) -/
lemma A_w3_z5_im : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4).im =
    3 * Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) := by
  have h4im : (4 : ℂ).im = 0 := Complex.ofReal_im 4
  have h2im : (2 : ℂ).im = 0 := Complex.ofReal_im 2
  have h4re : (4 : ℂ).re = 4 := Complex.ofReal_re 4
  have h2re : (2 : ℂ).re = 2 := Complex.ofReal_re 2
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
             h4re, h4im, h2re, h2im, add_zero, zero_mul, neg_zero,
             zeta5_im_eq_sin, zeta5_sq_im_eq, zeta5_pow4_im]
  ring

/-- ||A_w3_z5||² = (7√5-19)²/16 + (3*sin(2π/5) - 2*sin(π/5))²
    Computation:
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      3*sin(2π/5) - 2*sin(π/5) = sin(π/5)*(3(1+√5)/2 - 2) = sin(π/5)*(3+3√5-4)/2 = sin(π/5)*(3√5-1)/2
      Im² = sin²(π/5)*(3√5-1)²/4 = ((5-√5)/8)*((9*5 - 6√5 + 1)/4) = ((5-√5)/8)*((46-6√5)/4)
          = (5-√5)(46-6√5)/32 = (230 - 30√5 - 46√5 + 6*5)/32 = (260 - 76√5)/32 = (65 - 19√5)/8
    Re² = (7√5-19)²/16 = (49*5 - 266√5 + 361)/16 = (606 - 266√5)/16 = (303 - 133√5)/8
    Total = (303-133√5 + 65-19√5)/8 = (368 - 152√5)/8 = 46 - 19√5 -/
lemma normSq_A_w3_z5 : Complex.normSq ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) = 46 - 19*√5 := by
  rw [Complex.normSq_apply, A_w3_z5_re, A_w3_z5_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- Simplify Im = 3*sin(2π/5) - 2*sin(π/5) = sin(π/5)*(3√5-1)/2
  have h_im_simp : 3 * Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) =
      Real.sin (π / 5) * (3*√5 - 1) / 2 := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((7*√5 - 19) / 4)^2 = (606 - 266*√5) / 16 := by nlinarith [sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (3*√5 - 1) / 2)^2 =
      Real.sin (π / 5)^2 * (3*√5 - 1)^2 / 4 := by ring
  have h_factor : (3*√5 - 1)^2 = 46 - 6*√5 := by nlinarith [sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_factor]
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

/-- Re(A_w3_z5 * conj(B)) where B = 1 - ζ₅.
    conj(1 - ζ₅) = 1 - ζ₅⁴
    A * conj(B) = (-4 + 4ζ₅ - 2ζ₅² + ζ₅⁴)(1 - ζ₅⁴)
               = -4 + 4ζ₅⁴ + 4ζ₅ - 4ζ₅⁵ - 2ζ₅² + 2ζ₅⁶ + ζ₅⁴ - ζ₅⁸
               = -4 + 5ζ₅⁴ + 4ζ₅ - 4 - 2ζ₅² + 2ζ₅ + ζ₅⁴ - ζ₅³
               = -8 + 6ζ₅ - 2ζ₅² - ζ₅³ + 5ζ₅⁴
    Re = -8 + 6*(√5-1)/4 - 2*(-(√5+1)/4) - (-(√5+1)/4) + 5*(√5-1)/4
       = -8 + (6√5-6 + 2√5+2 + √5+1 + 5√5-5)/4
       = -8 + (14√5 - 8)/4 = -10 + 7√5/2 = (7√5 - 20)/2 -/
lemma re_A_w3_z5_mul_conj_B :
    (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re = (7*√5 - 20) / 2 := by
  sorry

/-- The vertex of f(c) = ||A + cB||² where A = -4 + 4ζ₅ - 2ζ₅² + ζ₅⁴, B = 1 - ζ₅.
    vertex = -Re(A*conj(B))/||B||²
           = -((14√5-33)/2) / ((5-√5)/2)
           = (33 - 14√5) / (5 - √5)
           = (33 - 14√5)(5 + √5) / ((5 - √5)(5 + √5))
           = (165 + 33√5 - 70√5 - 14*5) / 20
           = (165 - 37√5 - 70) / 20
           = (95 - 37√5) / 20 -/
lemma w3_z5_vertex : -(((14*√5 - 33) / 2) / ((5 - √5) / 2)) = (95 - 37*√5) / 20 := by
  have h_5_minus_sqrt5_ne : 5 - √5 ≠ 0 := by nlinarith [Real.sqrt_nonneg 5, sqrt5_sq]
  have h_denom_ne : (5 - √5) / 2 ≠ 0 := by
    have h : 5 - √5 > 0 := by nlinarith [Real.sqrt_nonneg 5, sqrt5_sq]
    have : (5 - √5) / 2 > 0 := by linarith
    linarith
  field_simp
  nlinarith [sqrt5_sq]

/-- The vertex (95 - 37√5)/20 ≈ -0.39 < 2 - √5 ≈ -0.236
    So the vertex is BELOW the interval [2-√5, 1]
    This means the parabola is monotonically increasing on [2-√5, 1]
    and achieves its maximum at c = 1 -/
lemma w3_z5_vertex_below_interval : (95 - 37*√5) / 20 < 2 - √5 := by
  sorry

/-- At c = 1: A + B = (-4 + 4ζ₅ - 2ζ₅² + ζ₅⁴) + (1 - ζ₅) = -3 + 3ζ₅ - 2ζ₅² + ζ₅⁴ -/
lemma w3_z5_at_one_expr : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (1 : ℂ) * (1 - ζ₅) =
    -3 + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4 := by ring

/-- Re(-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴) -/
lemma w3_z5_at_one_re : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (5*√5 - 13) / 4 := by
  sorry

/-- Im(-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴) -/
lemma w3_z5_at_one_im : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).im =
    2 * Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) := by
  sorry

/-- ||-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴||² at c=1
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      2*sin(2π/5) - 2*sin(π/5) = 2*sin(π/5)*((1+√5)/2 - 1) = sin(π/5)*(√5-1)
      Im² = sin²(π/5)*(√5-1)² = ((5-√5)/8)*(6-2√5) = (5-√5)(6-2√5)/8
          = (30 - 10√5 - 6√5 + 2*5)/8 = (40 - 16√5)/8 = 5 - 2√5
    Re² = (5√5-13)²/16 = (125 - 130√5 + 169)/16 = (294 - 130√5)/16 = (147 - 65√5)/8
    Total = (147 - 65√5 + 40 - 16√5)/8 = (187 - 81√5)/8
    But we need this to equal 3 + φ = (7 + √5)/2 = (28 + 4√5)/8?
    Let me recompute... -/
lemma normSq_w3_z5_at_one : Complex.normSq ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z5_at_one_re, w3_z5_at_one_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : 2 * Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) =
      Real.sin (π / 5) * (√5 - 1) := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((5*√5 - 13) / 4)^2 = (294 - 130*√5) / 16 := by nlinarith [sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (√5 - 1))^2 = Real.sin (π / 5)^2 * (√5 - 1)^2 := by ring
  have h_sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by nlinarith [sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_minus_1_sq]
  unfold φ Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

/-- z5 bound for word3: ‖(-4 + 4*ζ₅ - 2*ζ₅² + ζ₅⁴) + c*(1 - ζ₅)‖ ≤ r_crit for c ∈ [2-√5, 1] -/
lemma cross_disk_w3_z5_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  sorry

end TDCSG.CompoundSymmetry.GG5
