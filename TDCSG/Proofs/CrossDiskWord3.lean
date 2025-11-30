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
- `cross_disk_w3_z2_bound`: z2 bound
- `cross_disk_w3_z3_bound`: z3 bound
- `cross_disk_w3_z4_bound`: z4 bound
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

/-- Re(2 + ζ₅³ - 2ζ₅⁴) = (9 - 3√5)/4 -/
lemma A_w3_z2_re : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4).re = (9 - 3*√5) / 4 := by
  have h2re : (2 : ℂ).re = 2 := rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, h2re]
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [h2im, zero_mul, sub_zero]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(2 + ζ₅³ - 2ζ₅⁴) = 2*sin(2π/5) - sin(π/5) -/
lemma A_w3_z2_im : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4).im = 2 * Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  have h2im : (2 : ℂ).im = 0 := rfl
  have h2re : (2 : ℂ).re = 2 := rfl
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, h2im, h2re, zero_mul, add_zero]
  rw [zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

/-- |2 + ζ₅³ - 2ζ₅⁴|² = 26 - 11√5
    Re² = ((9-3√5)/4)² = (9-3√5)²/16 = (81 - 54√5 + 9*5)/16 = (126 - 54√5)/16
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      Im = 2*sin(π/5)*(1+√5)/2 - sin(π/5) = sin(π/5)*((1+√5) - 1) = sin(π/5)*√5
      Im² = sin²(π/5)*5 = ((5-√5)/8)*5 = (25-5√5)/8
    Total = (126-54√5)/16 + (25-5√5)/8 = (126-54√5 + 50-10√5)/16 = (176-64√5)/16 = 11 - 4√5
    Wait, let me recompute more carefully -/
lemma normSq_A_w3_z2 : Complex.normSq ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) = 11 - 4*√5 := by
  rw [Complex.normSq_apply, A_w3_z2_re, A_w3_z2_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- Im = 2*sin(2π/5) - sin(π/5) = 2*sin(π/5)*(1+√5)/2 - sin(π/5) = sin(π/5)*√5
  have h_im_simp : 2 * Real.sin (2 * π / 5) - Real.sin (π / 5) = Real.sin (π / 5) * √5 := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((9 - 3*√5) / 4)^2 = (126 - 54*√5) / 16 := by nlinarith [h_sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * √5)^2 = Real.sin (π / 5)^2 * 5 := by nlinarith [h_sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq]
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

/-- conj(ζ₅⁴ - 1) = ζ₅ - 1 -/
lemma conj_B3 : starRingEnd ℂ (ζ₅^4 - 1) = ζ₅ - 1 := by
  simp only [map_sub, map_one, map_pow, zeta5_conj]
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  calc (ζ₅^4)^4 - 1 = ζ₅^16 - 1 := by ring
    _ = ζ₅^(16 % 5) - 1 := by rw [zeta5_pow_reduce 16]
    _ = ζ₅ - 1 := by norm_num

/-- Re((2 + ζ₅³ - 2ζ₅⁴) * conj(ζ₅⁴ - 1)) = (3√5 - 10)/2
    conj(ζ₅⁴ - 1) = ζ₅ - 1
    (2 + ζ₅³ - 2ζ₅⁴) * (ζ₅ - 1) = 2ζ₅ - 2 + ζ₅⁴ - ζ₅³ - 2ζ₅⁵ + 2ζ₅⁴
                                 = 2ζ₅ - 2 + 3ζ₅⁴ - ζ₅³ - 2 (using ζ₅⁵ = 1)
                                 = 2ζ₅ - 4 + 3ζ₅⁴ - ζ₅³ -/
lemma re_A_w3_z2_mul_conj_B :
    (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re = (3*√5 - 10) / 2 := by
  rw [conj_B3]
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  have h_expand : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * (ζ₅ - 1) = 2*ζ₅ - 4 + 3*ζ₅^4 - ζ₅^3 := by
    calc ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * (ζ₅ - 1)
        = 2*ζ₅ - 2 + ζ₅^4 - ζ₅^3 - 2*ζ₅^5 + 2*ζ₅^4 := by ring
      _ = 2*ζ₅ - 2 + ζ₅^4 - ζ₅^3 - 2*1 + 2*ζ₅^4 := by rw [h5]
      _ = 2*ζ₅ - 4 + 3*ζ₅^4 - ζ₅^3 := by ring
  rw [h_expand]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re]
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  have h3re : (3 : ℂ).re = 3 := rfl
  have h3im : (3 : ℂ).im = 0 := rfl
  have h4re : (4 : ℂ).re = 4 := rfl
  simp only [h2re, h2im, h3re, h3im, h4re, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_pow4_re, zeta5_cubed_re]
  ring

/-- The vertex of f(c) = |A + cB|² where A = 2 + ζ₅³ - 2ζ₅⁴, B = ζ₅⁴ - 1.
    vertex = -Re(A*conj(B))/|B|² = -((3√5-10)/2) / ((5-√5)/2) = (10-3√5)/(5-√5)
           = (10-3√5)(5+√5)/20 = (50+10√5-15√5-15)/20 = (35-5√5)/20 = (7-√5)/4 -/
lemma w3_z2_vertex : -(((3*√5 - 10) / 2) / ((5 - √5) / 2)) = (7 - √5) / 4 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_5_minus_sqrt5_ne : 5 - √5 ≠ 0 := by nlinarith [Real.sqrt_nonneg 5]
  have h_denom_ne : (5 - √5) / 2 ≠ 0 := by
    have h : 5 - √5 > 0 := by nlinarith [Real.sqrt_nonneg 5, h_sqrt5_sq]
    have : (5 - √5) / 2 > 0 := by linarith
    linarith
  field_simp
  nlinarith [h_sqrt5_sq]

/-- The vertex (7-√5)/4 ≈ 1.19 > 1, so it is above the interval [2-√5, 1] -/
lemma w3_z2_vertex_above_interval : (7 - √5) / 4 > 1 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- Need: (7 - √5)/4 > 1 ⟺ 7 - √5 > 4 ⟺ 3 > √5 ⟺ 9 > 5 ✓
  nlinarith [h_sqrt5_sq]

/-- At c = 1: A + B = (2 + ζ₅³ - 2ζ₅⁴) + (ζ₅⁴ - 1) = 1 + ζ₅³ - ζ₅⁴ -/
lemma w3_z2_at_one_expr : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (1 : ℂ) * (ζ₅^4 - 1) = 1 + ζ₅^3 - ζ₅^4 := by
  ring

/-- Re(1 + ζ₅³ - ζ₅⁴) = 1 + (-(√5+1)/4) - (√5-1)/4 = 1 - √5/2 = (2-√5)/2 -/
lemma w3_z2_at_one_re : ((1 : ℂ) + ζ₅^3 - ζ₅^4).re = (2 - √5) / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(1 + ζ₅³ - ζ₅⁴) = -sin(π/5) + sin(2π/5) -/
lemma w3_z2_at_one_im : ((1 : ℂ) + ζ₅^3 - ζ₅^4).im = Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.one_im]
  rw [zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

/-- |1 + ζ₅³ - ζ₅⁴|² ≤ 3 + φ
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      Im = sin(π/5)*(1+√5)/2 - sin(π/5) = sin(π/5)*((1+√5)/2 - 1) = sin(π/5)*(√5-1)/2
      Im² = sin²(π/5)*(√5-1)²/4 = ((5-√5)/8)*(6-2√5)/4 = (5-√5)(3-√5)/16
          = (15 - 5√5 - 3√5 + 5)/16 = (20 - 8√5)/16 = (5 - 2√5)/4
    Re = (2 - √5)/2
    Re² = (2 - √5)²/4 = (4 - 4√5 + 5)/4 = (9 - 4√5)/4
    Total = (9 - 4√5 + 5 - 2√5)/4 = (14 - 6√5)/4 = (7 - 3√5)/2 -/
lemma normSq_w3_z2_at_one : Complex.normSq ((1 : ℂ) + ζ₅^3 - ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z2_at_one_re, w3_z2_at_one_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : Real.sin (2 * π / 5) - Real.sin (π / 5) =
      Real.sin (π / 5) * (√5 - 1) / 2 := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((2 - √5) / 2)^2 = (9 - 4*√5) / 4 := by nlinarith [h_sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (√5 - 1) / 2)^2 =
      Real.sin (π / 5)^2 * (√5 - 1)^2 / 4 := by ring
  have h_sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by nlinarith [h_sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_minus_1_sq]
  unfold φ Real.goldenRatio
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

/-- At c = 2-√5: A + (2-√5)B = √5 + ζ₅³ - √5*ζ₅⁴ -/
lemma w3_z2_at_lower_expr : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + ((2 - √5 : ℝ) : ℂ) * (ζ₅^4 - 1) =
    (√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4 := by
  push_cast
  ring

/-- Re(√5 + ζ₅³ - √5*ζ₅⁴) = √5 - (√5+1)/4 - √5*(√5-1)/4
                           = √5 - (√5+1)/4 - (5-√5)/4
                           = √5 - (√5+1+5-√5)/4
                           = √5 - 6/4 = √5 - 3/2 = (2√5 - 3)/2 -/
lemma w3_z2_at_lower_re : ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4).re = (2*√5 - 3) / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith [h_sqrt5_sq]

/-- Im(√5 + ζ₅³ - √5*ζ₅⁴) = -sin(π/5) - √5*(-sin(2π/5))
                           = -sin(π/5) + √5*sin(2π/5) -/
lemma w3_z2_at_lower_im : ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4).im =
    √5 * Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

/-- |√5 + ζ₅³ - √5*ζ₅⁴|² ≤ 3 + φ
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      Im = √5*sin(π/5)*(1+√5)/2 - sin(π/5)
         = sin(π/5)*(√5*(1+√5)/2 - 1)
         = sin(π/5)*((√5+5)/2 - 1)
         = sin(π/5)*(√5+3)/2
      Im² = sin²(π/5)*(√5+3)²/4 = ((5-√5)/8)*((5+6√5+9)/4)
          = ((5-√5)/8)*((14+6√5)/4) = (5-√5)(7+3√5)/16
          = (35 + 15√5 - 7√5 - 15)/16 = (20 + 8√5)/16 = (5 + 2√5)/4
    Re = (2√5 - 3)/2
    Re² = (2√5 - 3)²/4 = (20 - 12√5 + 9)/4 = (29 - 12√5)/4
    Total = (29 - 12√5 + 5 + 2√5)/4 = (34 - 10√5)/4 = (17 - 5√5)/2 -/
lemma normSq_w3_z2_at_lower : Complex.normSq ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z2_at_lower_re, w3_z2_at_lower_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : √5 * Real.sin (2 * π / 5) - Real.sin (π / 5) =
      Real.sin (π / 5) * (√5 + 3) / 2 := by
    rw [h_sin_double]
    -- LHS = √5 * sin(π/5) * (1+√5)/2 - sin(π/5) = sin(π/5) * [√5*(1+√5)/2 - 1]
    -- = sin(π/5) * [(√5 + 5)/2 - 1] = sin(π/5) * (√5 + 3)/2
    have h1 : √5 * (1 + √5) = √5 + 5 := by nlinarith [h_sqrt5_sq]
    calc √5 * (Real.sin (π / 5) * (1 + √5) / 2) - Real.sin (π / 5)
        = Real.sin (π / 5) * (√5 * (1 + √5) / 2 - 1) := by ring
      _ = Real.sin (π / 5) * ((√5 + 5) / 2 - 1) := by rw [h1]
      _ = Real.sin (π / 5) * (√5 + 3) / 2 := by ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((2*√5 - 3) / 2)^2 = (29 - 12*√5) / 4 := by nlinarith [h_sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (√5 + 3) / 2)^2 =
      Real.sin (π / 5)^2 * (√5 + 3)^2 / 4 := by ring
  have h_sqrt5_plus_3_sq : (√5 + 3)^2 = 14 + 6*√5 := by nlinarith [h_sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_plus_3_sq]
  unfold φ Real.goldenRatio
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

set_option maxHeartbeats 800000 in
/-- z2 bound for word3: ‖(2 + ζ₅³ - 2*ζ₅⁴) + c*(ζ₅⁴ - 1)‖ ≤ r_crit for c ∈ [2-√5, 1]

The proof uses:
- f(c) = |A + cB|² is quadratic with vertex at (7 - √5)/4 ≈ 1.19 > 1
- Since vertex > 1 and parabola opens upward, f is decreasing on [2-√5, 1]
- Maximum is at c = 2-√5
- Both endpoints satisfy f ≤ 3+φ, hence all c in [2-√5, 1] satisfy it -/
lemma cross_disk_w3_z2_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  set A : ℂ := (2 : ℂ) + ζ₅^3 - 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  -- Value at c = 1
  have h_at_one : ‖A + (1 : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z2_at_one_expr]
    exact normSq_w3_z2_at_one

  -- Value at c = 2 - √5
  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z2_at_lower_expr]
    exact normSq_w3_z2_at_lower

  have h_normSq_B := normSq_B3
  have h_normSq_A := normSq_A_w3_z2
  have h_re_AB := re_A_w3_z2_mul_conj_B
  have h_vertex := w3_z2_vertex_above_interval

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

  have h_coeff_a : Complex.normSq (ζ₅^4 - 1) = (5 - √5) / 2 := normSq_B3
  have h_coeff_b : (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re = (3*√5 - 10) / 2 := re_A_w3_z2_mul_conj_B
  have h_coeff_c : Complex.normSq ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) = 11 - 4*√5 := normSq_A_w3_z2

  have h_f_le_max : Complex.normSq (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)) ≤ 3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = (2 : ℂ) + ζ₅^3 - 2*ζ₅^4 by rfl, show B = ζ₅^4 - 1 by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    -- f(c) = 11 - 4√5 + 2c*(3√5-10)/2 + c²*(5-√5)/2
    --      = 11 - 4√5 + c*(3√5-10) + c²*(5-√5)/2

    -- Since f is decreasing on [2-√5, 1] (vertex > 1), f(c) ≤ f(2-√5) for all c ≥ 2-√5
    have h_f_mono : ∀ c₁ c₂ : ℝ, c₁ ≤ c₂ → c₂ ≤ 1 →
        11 - 4*√5 + 2 * c₂ * ((3*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2) ≤
        11 - 4*√5 + 2 * c₁ * ((3*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2) := by
      intro c₁ c₂ hc12 hc2_le1
      have h_diff : (11 - 4*√5 + 2 * c₂ * ((3*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2)) -
                    (11 - 4*√5 + 2 * c₁ * ((3*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2)) =
                    (c₂ - c₁) * ((3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
      -- Need: (c₂ - c₁) * ((3√5-10) + (c₁+c₂)*(5-√5)/2) ≤ 0
      -- Since c₂ ≥ c₁, need: (3√5-10) + (c₁+c₂)*(5-√5)/2 ≤ 0
      -- At c₁+c₂ = 2: (3√5-10) + 2*(5-√5)/2 = 3√5-10 + 5-√5 = 2√5-5 ≈ -0.53 < 0
      have h_sum_bound : c₁ + c₂ ≤ 2 := by linarith
      have h_factor_neg : (3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
        have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [h_sqrt5_sq]
        -- At c₁+c₂ = 2: (3√5-10) + 2*(5-√5)/2 = 3√5-10 + 5-√5 = 2√5-5 < 0
        calc (3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)
            ≤ (3*√5 - 10) + 2 * ((5 - √5) / 2) := by gcongr
          _ = 2*√5 - 5 := by ring
          _ ≤ 0 := by nlinarith [h_sqrt5_sq]
      nlinarith [hc12, h_factor_neg]

    calc 11 - 4*√5 + 2 * c * ((3*√5 - 10) / 2) + c^2 * ((5 - √5) / 2)
        ≤ 11 - 4*√5 + 2 * (2 - √5) * ((3*√5 - 10) / 2) + (2 - √5)^2 * ((5 - √5) / 2) := by
          apply h_f_mono (2 - √5) c (by linarith [hc_lo]) hc_hi
      _ ≤ 3 + φ := by
          have h_eq : 11 - 4*√5 + 2 * (2 - √5) * ((3*√5 - 10) / 2) + (2 - √5)^2 * ((5 - √5) / 2) =
                      Complex.normSq ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4) := by
            rw [Complex.normSq_apply, w3_z2_at_lower_re, w3_z2_at_lower_im]
            simp only [← sq]
            have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
              rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
              rw [Real.cos_pi_div_five]
              ring
            have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
            have h_im_simp : √5 * Real.sin (2 * π / 5) - Real.sin (π / 5) =
                Real.sin (π / 5) * (√5 + 3) / 2 := by
              rw [h_sin_double]
              -- LHS = √5 * (sin(π/5) * (1+√5) / 2) - sin(π/5)
              --     = sin(π/5) * (√5 * (1+√5) / 2 - 1)
              --     = sin(π/5) * ((√5 + √5^2) / 2 - 1)
              --     = sin(π/5) * ((√5 + 5) / 2 - 1)
              --     = sin(π/5) * ((√5 + 3) / 2)
              have h_sqrt5_prod : √5 * (1 + √5) = √5 + 5 := by nlinarith [h_sqrt5_sq]
              calc √5 * (Real.sin (π / 5) * (1 + √5) / 2) - Real.sin (π / 5)
                  = Real.sin (π / 5) * (√5 * (1 + √5) / 2 - 1) := by ring
                _ = Real.sin (π / 5) * ((√5 + 5) / 2 - 1) := by rw [h_sqrt5_prod]
                _ = Real.sin (π / 5) * (√5 + 3) / 2 := by ring
            rw [h_im_simp]
            have h_im_sq : (Real.sin (π / 5) * (√5 + 3) / 2)^2 =
                Real.sin (π / 5)^2 * (√5 + 3)^2 / 4 := by ring
            have h_sqrt5_plus_3_sq : (√5 + 3)^2 = 14 + 6*√5 := by nlinarith [h_sqrt5_sq]
            rw [h_im_sq, h_sin_sq, h_sqrt5_plus_3_sq]
            nlinarith [h_sqrt5_sq]
          rw [h_eq]
          exact normSq_w3_z2_at_lower

  exact h_f_le_max

/-! ### Word3 z3 helper lemmas -/

/-- Re(-2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴) = (3√5 - 9)/4 -/
lemma A_w3_z3_re : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4).re = (3*√5 - 9) / 4 := by
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
             h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(-2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴) = 3*sin(π/5) - 2*sin(2π/5) -/
lemma A_w3_z3_im : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4).im =
    3 * Real.sin (π / 5) - 2 * Real.sin (2 * π / 5) := by
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
             h2re, h2im, zero_mul, add_zero]
  rw [zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im']
  ring

/-- |A|² for A = -2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴
    Re² = ((3√5-9)/4)² = (9*5 - 54√5 + 81)/16 = (126 - 54√5)/16
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      Im = 3*sin(π/5) - 2*sin(π/5)*(1+√5)/2 = sin(π/5)*(3 - (1+√5)) = sin(π/5)*(2 - √5)
      Im² = sin²(π/5)*(2-√5)² = ((5-√5)/8)*(9-4√5)
      (5-√5)(9-4√5) = 45 - 20√5 - 9√5 + 4*5 = 65 - 29√5
      Im² = (65 - 29√5)/8
    Total = (126-54√5)/16 + (130-58√5)/16 = (256-112√5)/16 = 16 - 7√5 -/
lemma normSq_A_w3_z3 : Complex.normSq ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) = 16 - 7*√5 := by
  rw [Complex.normSq_apply, A_w3_z3_re, A_w3_z3_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- Im = 3*sin(π/5) - 2*sin(π/5)*(1+√5)/2 = sin(π/5)*(3 - (1+√5)) = sin(π/5)*(2 - √5)
  have h_im_simp : 3 * Real.sin (π / 5) - 2 * Real.sin (2 * π / 5) =
      Real.sin (π / 5) * (2 - √5) := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((3*√5 - 9) / 4)^2 = (126 - 54*√5) / 16 := by nlinarith [h_sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (2 - √5))^2 = Real.sin (π / 5)^2 * (2 - √5)^2 := by ring
  have h_2_minus_sqrt5_sq : (2 - √5)^2 = 9 - 4*√5 := by nlinarith [h_sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_2_minus_sqrt5_sq]
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

/-- conj(ζ₅³ - ζ₅⁴) = ζ₅² - ζ₅ -/
lemma conj_B_z3 : starRingEnd ℂ (ζ₅^3 - ζ₅^4) = ζ₅^2 - ζ₅ := by
  rw [map_sub]
  have h3 : starRingEnd ℂ (ζ₅^3) = ζ₅^2 := by
    rw [map_pow, zeta5_conj]
    calc (ζ₅^4)^3 = ζ₅^12 := by ring
      _ = ζ₅^2 := zeta5_pow_twelve
  have h4 : starRingEnd ℂ (ζ₅^4) = ζ₅ := by
    rw [map_pow, zeta5_conj]
    calc (ζ₅^4)^4 = ζ₅^16 := by ring
      _ = ζ₅ := zeta5_pow_sixteen
  rw [h3, h4]

/-- Re(A * conj(B)) = (5√5 - 10)/2 for A = -2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴, B = ζ₅³ - ζ₅⁴
    A * conj(B) = (-2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴) * (ζ₅² - ζ₅)
    Expanding with ζ₅⁵=1, ζ₅⁶=ζ₅: -4 + 4ζ₅ - 2ζ₅² - ζ₅³ + 3ζ₅⁴ -/
lemma re_A_w3_z3_mul_conj_B :
    (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re = (5*√5 - 10) / 2 := by
  rw [conj_B_z3]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  -- A * (ζ₅² - ζ₅) = (-2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴) * (ζ₅² - ζ₅)
  -- Expanding: -2ζ₅² + 2ζ₅ + ζ₅⁴ - ζ₅³ - 2ζ₅⁵ + 2ζ₅⁴ + 2ζ₅⁶ - 2ζ₅⁵
  -- = -2ζ₅² + 2ζ₅ + ζ₅⁴ - ζ₅³ - 2 + 2ζ₅⁴ + 2ζ₅ - 2 = -4 + 4ζ₅ - 2ζ₅² - ζ₅³ + 3ζ₅⁴
  have h_expand : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * (ζ₅^2 - ζ₅) =
      -4 + 4*ζ₅ - 2*ζ₅^2 - ζ₅^3 + 3*ζ₅^4 := by
    have h6 : ζ₅^6 = ζ₅ := by rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, h5, one_mul, pow_one]
    calc ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * (ζ₅^2 - ζ₅)
        = -2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 - 2*ζ₅^5 + 2*ζ₅^4 + 2*ζ₅^6 - 2*ζ₅^5 := by ring
      _ = -2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 - 2*1 + 2*ζ₅^4 + 2*ζ₅ - 2*1 := by rw [h5, h6]
      _ = -4 + 4*ζ₅ - 2*ζ₅^2 - ζ₅^3 + 3*ζ₅^4 := by ring
  rw [h_expand]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re]
  have h4re : (4 : ℂ).re = 4 := rfl
  have h4im : (4 : ℂ).im = 0 := rfl
  have h3re : (3 : ℂ).re = 3 := rfl
  have h3im : (3 : ℂ).im = 0 := rfl
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [h4re, h4im, h3re, h3im, h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Vertex of quadratic f(c) = |A + cB|² is at (5 - 3√5)/4
    vertex = -Re(A*conj(B)) / |B|² = -((5√5-10)/2) / ((5-√5)/2) = (10-5√5)/(5-√5)
    = 5(2-√5)/(5-√5) = (10 - 5√5) / (5 - √5) -/
lemma w3_z3_vertex : -(((5*√5 - 10) / 2) / ((5 - √5) / 2)) = (5 - 3*√5) / 4 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_denom_ne : 5 - √5 ≠ 0 := by nlinarith [h_sqrt5_sq]
  -- -((5√5 - 10)/2) / ((5 - √5)/2) = -(5√5 - 10)/(5 - √5) = (10 - 5√5)/(5 - √5)
  -- = 5(2 - √5)/(5 - √5)
  -- Multiplying num and denom by (5 + √5): 5(2-√5)(5+√5)/((5-√5)(5+√5))
  -- = 5(10 + 2√5 - 5√5 - 5)/(25 - 5) = 5(5 - 3√5)/20 = (5 - 3√5)/4
  field_simp
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

/-- The vertex (5 - 3√5)/4 ≈ -0.427 is below the interval [2-√5, 1], since 2-√5 ≈ -0.236 -/
lemma w3_z3_vertex_below_interval : (5 - 3*√5) / 4 < 2 - √5 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- (5 - 3√5)/4 < 2 - √5 iff 5 - 3√5 < 8 - 4√5 iff √5 < 3 iff 5 < 9
  nlinarith [h_sqrt5_sq]

/-- Expression at c = 1: A + B = -2 + ζ₅² - 2ζ₅³ + 2ζ₅⁴ + ζ₅³ - ζ₅⁴ = -2 + ζ₅² - ζ₅³ + ζ₅⁴ -/
lemma w3_z3_at_one_expr : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (1 : ℂ) * (ζ₅^3 - ζ₅^4) =
    -2 + ζ₅^2 - ζ₅^3 + ζ₅^4 := by ring

/-- Re(-2 + ζ₅² - ζ₅³ + ζ₅⁴) = (√5 - 9)/4 -/
lemma w3_z3_at_one_re : ((-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4).re = (√5 - 9) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  have h2re : (2 : ℂ).re = 2 := rfl
  rw [h2re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(-2 + ζ₅² - ζ₅³ + ζ₅⁴) = 2*sin(π/5) - sin(2π/5) -/
lemma w3_z3_at_one_im : ((-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4).im =
    2 * Real.sin (π / 5) - Real.sin (2 * π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im]
  have h2im : (2 : ℂ).im = 0 := rfl
  rw [h2im, zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im']
  ring

/-- |A + B|² at c=1: |-2 + ζ₅² - ζ₅³ + ζ₅⁴|²
    Re² = ((√5-9)/4)² = (86 - 18√5)/16
    Im = 2*sin(π/5) - sin(2π/5) = 2*sin(π/5) - sin(π/5)*(1+√5)/2 = sin(π/5)*(3-√5)/2
    Im² = sin²(π/5)*(3-√5)²/4 = ((5-√5)/8)*(14-6√5)/4 = (5-√5)(14-6√5)/32
    Total ≤ 3+φ -/
lemma normSq_w3_z3_at_one : Complex.normSq ((-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z3_at_one_re, w3_z3_at_one_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- Im = 2*sin(π/5) - sin(π/5)*(1+√5)/2 = sin(π/5)*(4 - (1+√5))/2 = sin(π/5)*(3-√5)/2
  have h_im_simp : 2 * Real.sin (π / 5) - Real.sin (2 * π / 5) =
      Real.sin (π / 5) * (3 - √5) / 2 := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((√5 - 9) / 4)^2 = (86 - 18*√5) / 16 := by nlinarith [h_sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (3 - √5) / 2)^2 =
      Real.sin (π / 5)^2 * (3 - √5)^2 / 4 := by ring
  have h_3_minus_sqrt5_sq : (3 - √5)^2 = 14 - 6*√5 := by nlinarith [h_sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_3_minus_sqrt5_sq]
  unfold φ
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5, Real.goldenRatio_pos]

/-- Expression at c = 2-√5: A + (2-√5)*B where A = -2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴, B = ζ₅³ - ζ₅⁴
    = -2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴ + (2-√5)*ζ₅³ - (2-√5)*ζ₅⁴
    = -2 + ζ₅² + (-2 + 2 - √5)*ζ₅³ + (2 - 2 + √5)*ζ₅⁴
    = -2 + ζ₅² - √5*ζ₅³ + √5*ζ₅⁴ -/
lemma w3_z3_at_lower_expr :
    ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + ((2 - √5 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4) =
    (-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4 := by
  push_cast
  ring

/-- Re at c = 2-√5: Re(-2 + ζ₅² - √5*ζ₅³ + √5*ζ₅⁴)
    = -2 + (-(√5+1)/4) - √5*(-(√5+1)/4) + √5*((√5-1)/4)
    = -2 + (-(√5+1)/4) + √5*(√5+1)/4 + √5*(√5-1)/4
    = -2 + (-(√5+1) + √5*(√5+1) + √5*(√5-1))/4
    = -2 + (-(√5+1) + 5 + √5 + 5 - √5)/4
    = -2 + (-√5 - 1 + 10)/4 = -2 + (9 - √5)/4 = (-8 + 9 - √5)/4 = (1 - √5)/4 -/
lemma w3_z3_at_lower_re :
    ((-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4).re = (1 - √5) / 4 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
             Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h2re : (2 : ℂ).re = 2 := rfl
  rw [h2re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  nlinarith [h_sqrt5_sq]

/-- Im at c = 2-√5: Im(-2 + ζ₅² - √5*ζ₅³ + √5*ζ₅⁴)
    = sin(π/5) - √5*(-sin(π/5)) + √5*(-sin(2π/5))
    = sin(π/5) + √5*sin(π/5) - √5*sin(2π/5)
    = sin(π/5)*(1 + √5) - √5*sin(π/5)*(1+√5)/2
    = sin(π/5)*(1 + √5)*(1 - √5/2)
    = sin(π/5)*(1 + √5)*(2 - √5)/2
    = sin(π/5)*(2 - √5 + 2√5 - 5)/2
    = sin(π/5)*(√5 - 3)/2 -/
lemma w3_z3_at_lower_im :
    ((-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4).im =
    Real.sin (π / 5) * (√5 - 3) / 2 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
             Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have h2im : (2 : ℂ).im = 0 := rfl
  rw [h2im, zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im']
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  rw [h_sin_double]
  -- After substitution: sin(π/5) + √5*sin(π/5) - √5*sin(π/5)*(1+√5)/2
  -- = sin(π/5)*(1 + √5 - √5*(1+√5)/2)
  -- Set s = sin(π/5) for clarity
  set s := Real.sin (π / 5) with hs_def
  -- LHS = s + √5*s - √5*s*(1+√5)/2 = s*(1 + √5 - √5*(1+√5)/2)
  -- = s*(1 + √5 - (√5 + √5²)/2) = s*(1 + √5 - (√5 + 5)/2)
  -- = s*((2 + 2√5 - √5 - 5)/2) = s*((-3 + √5)/2) = s*(√5 - 3)/2
  have h_factor : s + √5 * s - √5 * (s * (1 + √5) / 2) = s * (√5 - 3) / 2 := by
    have h_expand : √5 * (s * (1 + √5) / 2) = s * √5 * (1 + √5) / 2 := by ring
    rw [h_expand]
    have h_sqrt5_times : √5 * (1 + √5) = √5 + 5 := by nlinarith [h_sqrt5_sq]
    calc s + √5 * s - s * √5 * (1 + √5) / 2
        = s + √5 * s - s * (√5 * (1 + √5)) / 2 := by ring
      _ = s + √5 * s - s * (√5 + 5) / 2 := by rw [h_sqrt5_times]
      _ = s * (√5 - 3) / 2 := by ring
  convert h_factor using 1; ring

/-- |A + (2-√5)*B|² at c = 2-√5 ≤ 3+φ
    Re² = ((1-√5)/4)² = (6 - 2√5)/16 = (3 - √5)/8
    Im² = (sin(π/5)*(√5-3)/2)² = sin²(π/5)*(14-6√5)/4 = ((5-√5)/8)*(14-6√5)/4
    Total = (3 - √5)/8 + (5-√5)(14-6√5)/32
    Need to show ≤ 3+φ = (7+√5)/2 -/
lemma normSq_w3_z3_at_lower :
    Complex.normSq ((-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z3_at_lower_re, w3_z3_at_lower_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  simp only [← sq]
  have h_re_sq : ((1 - √5) / 4)^2 = (6 - 2*√5) / 16 := by nlinarith [h_sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (√5 - 3) / 2)^2 =
      Real.sin (π / 5)^2 * (√5 - 3)^2 / 4 := by ring
  have h_sqrt5_minus_3_sq : (√5 - 3)^2 = 14 - 6*√5 := by nlinarith [h_sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_minus_3_sq]
  unfold φ
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5, Real.goldenRatio_pos]

set_option maxHeartbeats 800000 in
/-- z3 bound for word3: ‖(-2 + ζ₅² - 2*ζ₅³ + 2*ζ₅⁴) + c*(ζ₅³ - ζ₅⁴)‖ ≤ r_crit for c ∈ [2-√5, 1]

The proof uses:
- f(c) = |A + cB|² is quadratic with vertex at (5 - 3√5)/4 ≈ -0.427 < 2-√5
- Since vertex < 2-√5 and parabola opens upward, f is increasing on [2-√5, 1]
- Maximum is at c = 1
- Both endpoints satisfy f ≤ 3+φ, hence all c in [2-√5, 1] satisfy it -/
lemma cross_disk_w3_z3_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by
  set A : ℂ := ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) with hA_def
  set B : ℂ := ζ₅^3 - ζ₅^4 with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  -- Value at c = 1
  have h_at_one : ‖A + (1 : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z3_at_one_expr]
    exact normSq_w3_z3_at_one

  -- Value at c = 2 - √5
  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z3_at_lower_expr]
    exact normSq_w3_z3_at_lower

  have h_normSq_B := normSq_B
  have h_normSq_A := normSq_A_w3_z3
  have h_re_AB := re_A_w3_z3_mul_conj_B
  have h_vertex := w3_z3_vertex_below_interval

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

  have h_coeff_a : Complex.normSq (ζ₅^3 - ζ₅^4) = (5 - √5) / 2 := normSq_B
  have h_coeff_b : (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re =
      (5*√5 - 10) / 2 := re_A_w3_z3_mul_conj_B
  have h_coeff_c : Complex.normSq ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) = 16 - 7*√5 := normSq_A_w3_z3

  have h_f_le_max : Complex.normSq (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (c : ℂ) * (ζ₅^3 - ζ₅^4)) ≤
      3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) by rfl, show B = ζ₅^3 - ζ₅^4 by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    -- f(c) = 16 - 7√5 + 2c*(5√5-10)/2 + c²*(5-√5)/2
    --      = 16 - 7√5 + c*(5√5-10) + c²*(5-√5)/2

    -- Since f is increasing on [2-√5, 1] (vertex < 2-√5), f(c) ≤ f(1) for all c ≤ 1
    have h_f_mono : ∀ c₁ c₂ : ℝ, 2 - √5 ≤ c₁ → c₁ ≤ c₂ →
        16 - 7*√5 + 2 * c₁ * ((5*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2) ≤
        16 - 7*√5 + 2 * c₂ * ((5*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2) := by
      intro c₁ c₂ hc1_lo hc12
      have h_diff : (16 - 7*√5 + 2 * c₂ * ((5*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2)) -
                    (16 - 7*√5 + 2 * c₁ * ((5*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2)) =
                    (c₂ - c₁) * ((5*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
      -- Need: (c₂ - c₁) * ((5√5-10) + (c₁+c₂)*(5-√5)/2) ≥ 0
      -- Since c₂ ≥ c₁, need: (5√5-10) + (c₁+c₂)*(5-√5)/2 ≥ 0
      -- Vertex is at c_v = (5-3√5)/4. For c₁, c₂ ≥ 2-√5 > c_v, the quadratic is increasing.
      -- The derivative is 2*(5√5-10)/2 + 2c*(5-√5)/2 = (5√5-10) + c*(5-√5)
      -- At c = 2-√5: (5√5-10) + (2-√5)*(5-√5) = 5√5 - 10 + 10 - 7√5 + 5 = 5 - 2√5
      -- Since √5 ≈ 2.236, 5 - 2√5 ≈ 0.53 > 0, so derivative is positive for c ≥ 2-√5
      have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [h_sqrt5_sq]
      have h_sum_ge : c₁ + c₂ ≥ 2 * (2 - √5) := by linarith
      have h_factor_nonneg : (5*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2) ≥ 0 := by
        -- At c₁ + c₂ = 2*(2-√5) = 4 - 2√5:
        -- (5√5-10) + (4-2√5)*(5-√5)/2 = (5√5-10) + (20 - 4√5 - 10√5 + 2*5)/2
        --                              = (5√5-10) + (30 - 14√5)/2 = (5√5-10) + 15 - 7√5
        --                              = 5 - 2√5 > 0 (since √5 < 2.5)
        calc (5*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)
            ≥ (5*√5 - 10) + 2 * (2 - √5) * ((5 - √5) / 2) := by gcongr
          _ = (5*√5 - 10) + (2 - √5) * (5 - √5) := by ring
          _ = 5 - 2*√5 := by nlinarith [h_sqrt5_sq]
          _ ≥ 0 := by nlinarith [h_sqrt5_sq]
      nlinarith [hc12, h_factor_nonneg]

    -- f(1) = 16 - 7√5 + 5√5 - 10 + (5-√5)/2 = 6 - 2√5 + (5-√5)/2 = (17 - 5√5)/2
    -- But 3 + φ = 3 + (1+√5)/2 = (7+√5)/2
    -- We need f(1) ≤ 3 + φ: (17 - 5√5)/2 ≤ (7+√5)/2 iff 17 - 5√5 ≤ 7 + √5 iff 10 ≤ 6√5 iff 5/3 ≤ √5
    -- Since √5 ≈ 2.236 > 5/3 ≈ 1.67, this is true
    have h_f_at_1_le : 16 - 7*√5 + 2 * 1 * ((5*√5 - 10) / 2) + 1^2 * ((5 - √5) / 2) ≤ 3 + φ := by
      unfold φ
      nlinarith [h_sqrt5_sq, Real.goldenRatio_pos]

    calc 16 - 7*√5 + 2 * c * ((5*√5 - 10) / 2) + c^2 * ((5 - √5) / 2)
        ≤ 16 - 7*√5 + 2 * 1 * ((5*√5 - 10) / 2) + 1^2 * ((5 - √5) / 2) := by
          apply h_f_mono c 1 hc_lo hc_hi
      _ ≤ 3 + φ := h_f_at_1_le

  exact h_f_le_max

/-! ### Word3 z4 helper lemmas -/

/-- Re(4 - 2*ζ₅ + ζ₅³ - 2*ζ₅⁴) = (19 - 5√5)/4 -/
lemma A_w3_z4_re : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).re = (19 - 5*√5) / 4 := by
  have h4re : (4 : ℂ).re = 4 := rfl
  have h4im : (4 : ℂ).im = 0 := rfl
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, h4re, h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(4 - 2*ζ₅ + ζ₅³ - 2*ζ₅⁴) = -sin(π/5) -/
lemma A_w3_z4_im : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).im = -Real.sin (π / 5) := by
  have h4im : (4 : ℂ).im = 0 := Complex.ofReal_im 4
  have h2re : (2 : ℂ).re = 2 := Complex.ofReal_re 2
  have h2im : (2 : ℂ).im = 0 := Complex.ofReal_im 2
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
             h2re, h2im, add_zero, zero_mul,
             zeta5_im_eq_sin, zeta5_cubed_im, zeta5_pow4_im, h4im]
  -- sin(6π/5) = -sin(π/5)
  have h_sin6 : Real.sin (6 * π / 5) = -Real.sin (π / 5) := by
    rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring, Real.sin_add_pi]
  rw [h_sin6]
  ring

/-- ||A_w3_z4||² = 31 - 12√5 -/
lemma normSq_A_w3_z4 : Complex.normSq ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) = 31 - 12*√5 := by
  rw [Complex.normSq_apply, A_w3_z4_re, A_w3_z4_im]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  simp only [← sq]
  rw [neg_sq, h_sin_sq]
  nlinarith [h_sqrt5_sq]

/-- Re((4 - 2*ζ₅ + ζ₅³ - 2*ζ₅⁴) * conj(ζ₅⁴ - 1)) = (6√5 - 15)/2 -/
lemma re_A_w3_z4_mul_conj_B : (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re =
    (6*√5 - 15) / 2 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  rw [conj_B3]  -- conj(ζ₅^4 - 1) = ζ₅ - 1
  -- Re(A * (ζ₅ - 1)) = Re(A)*Re(ζ₅ - 1) - Im(A)*Im(ζ₅ - 1) = A.re*(ζ₅.re - 1) - A.im*ζ₅.im
  have hA_re : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).re = (19 - 5*√5) / 4 := A_w3_z4_re
  have hA_im : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).im = -Real.sin (π / 5) := A_w3_z4_im
  have hB_re : (ζ₅ - 1 : ℂ).re = ζ₅.re - 1 := by simp only [Complex.sub_re, Complex.one_re]
  have hB_im : (ζ₅ - 1 : ℂ).im = ζ₅.im := by simp only [Complex.sub_im, Complex.one_im, sub_zero]
  rw [Complex.mul_re, hA_re, hA_im, hB_re, hB_im, zeta5_re, zeta5_im_eq_sin]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- sin(2π/5) = sin(π/5) * (1 + √5) / 2
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  rw [h_sin_double]
  -- Now: (19 - 5√5)/4 * ((√5-1)/4 - 1) - (-sin(π/5)) * sin(π/5) * (1+√5)/2
  -- Rewrite sin*sin as sin² so we can substitute h_sin_sq
  have h_expand : -Real.sin (π / 5) * (Real.sin (π / 5) * (1 + √5) / 2) =
      -Real.sin (π / 5)^2 * (1 + √5) / 2 := by ring
  rw [h_expand, h_sin_sq]
  -- Now all sin terms are eliminated, pure √5 arithmetic
  nlinarith [h_sqrt5_sq]

/-- Vertex of z4 quadratic is at c_v = (15 - 6√5)/(5 - √5) ≈ 0.57, which is in [2-√5, 1] -/
lemma w3_z4_vertex : -(((6*√5 - 15) / 2) / ((5 - √5) / 2)) = (15 - 6*√5) / (5 - √5) := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_denom_ne : (5 - √5) / 2 ≠ 0 := by nlinarith [h_sqrt5_sq]
  field_simp
  ring

/-- At c=1: A + B = (4 - 2*ζ₅ + ζ₅³ - 2*ζ₅⁴) + (ζ₅⁴ - 1) = 3 - 2*ζ₅ + ζ₅³ - ζ₅⁴ -/
lemma w3_z4_at_one_expr : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (1 : ℂ) * (ζ₅^4 - 1) =
    3 - 2*ζ₅ + ζ₅^3 - ζ₅^4 := by ring

/-- Re(3 - 2*ζ₅ + ζ₅³ - ζ₅⁴) = 7/2 - √5 -/
lemma w3_z4_at_one_re : ((3 : ℂ) - 2*ζ₅ + ζ₅^3 - ζ₅^4).re = 7/2 - √5 := by
  have h3re : (3 : ℂ).re = 3 := by norm_num
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have h2im : (2 : ℂ).im = 0 := by norm_num
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, h3re, h2re, h2im, zeta5_re,
    zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(3 - 2*ζ₅ + ζ₅³ - ζ₅⁴) = -sin(2π/5) - sin(π/5) -/
lemma w3_z4_at_one_im : ((3 : ℂ) - 2*ζ₅ + ζ₅^3 - ζ₅^4).im =
    -Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  have h3im : (3 : ℂ).im = 0 := by norm_num
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have h2im : (2 : ℂ).im = 0 := by norm_num
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, h3im, h2re, h2im, zeta5_im_eq_sin,
    zeta5_cubed_im, zeta5_pow4_im]
  -- sin(6π/5) = -sin(π/5)
  have h_sin6 : Real.sin (6 * π / 5) = -Real.sin (π / 5) := by
    rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring, Real.sin_add_pi]
  rw [h_sin6]
  ring

/-- ||3 - 2*ζ₅ + ζ₅³ - ζ₅⁴||² ≤ 3 + φ -/
lemma normSq_w3_z4_at_one : Complex.normSq ((3 : ℂ) - 2*ζ₅ + ζ₅^3 - ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z4_at_one_re, w3_z4_at_one_im]
  -- (7/2 - √5)² + (sin(2π/5) + sin(π/5))²
  -- sin(2π/5) = 2*sin(π/5)*cos(π/5) = 2*sin(π/5)*(1+√5)/4 = sin(π/5)*(1+√5)/2
  -- sin(2π/5) + sin(π/5) = sin(π/5)*(1 + (1+√5)/2) = sin(π/5)*(3+√5)/2
  -- Im² = sin²(π/5)*(3+√5)²/4 = ((5-√5)/8)*((3+√5)²/4)
  -- (3+√5)² = 9 + 6√5 + 5 = 14 + 6√5
  -- Im² = (5-√5)*(14+6√5)/32 = (70 + 30√5 - 14√5 - 6*5)/32 = (40 + 16√5)/32 = (5 + 2√5)/4
  -- Re² = (7/2 - √5)² = 49/4 - 7√5 + 5 = 69/4 - 7√5
  -- Total = 69/4 - 7√5 + (5 + 2√5)/4 = 74/4 - 7√5 + 2√5/4 = 74/4 - 26√5/4 = (74 - 26√5)/4
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  simp only [← sq]
  rw [h_sin_double]
  -- Now goal: (7/2 - √5)² + (-(sin(π/5)*(1+√5)/2) - sin(π/5))² ≤ 3 + φ
  have h_im_simp : -(Real.sin (π / 5) * (1 + √5) / 2) - Real.sin (π / 5) =
      -Real.sin (π / 5) * (3 + √5) / 2 := by ring
  rw [h_im_simp]
  have h_neg_sq : (-Real.sin (π / 5) * (3 + √5) / 2)^2 =
      Real.sin (π / 5)^2 * (3 + √5)^2 / 4 := by ring
  rw [h_neg_sq, h_sin_sq]
  unfold φ goldenRatio
  -- Goal: (7/2 - √5)² + (5-√5)*(3+√5)²/32 ≤ (7+√5)/2
  -- Expand and simplify to: (74 - 26√5)/4 ≤ (14 + 2√5)/4
  -- Which simplifies to: 60 ≤ 28√5, i.e., 15/7 ≤ √5
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5, sq_nonneg (7*√5 - 15)]

/-- z4 bound for word3: ‖(4 - 2*ζ₅ + ζ₅³ - 2*ζ₅⁴) + c*(ζ₅⁴ - 1)‖ ≤ r_crit for c ∈ [2-√5, 1]
Uses that the quadratic has vertex in the interval but the bound still holds at the vertex. -/
lemma cross_disk_w3_z4_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  set A : ℂ := (4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  have h_normSq_B := normSq_B3
  have h_normSq_A := normSq_A_w3_z4
  have h_re_AB := re_A_w3_z4_mul_conj_B

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

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (ζ₅^4 - 1) = (5 - √5) / 2 := normSq_B3
  have h_coeff_b : (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re =
      (6*√5 - 15) / 2 := re_A_w3_z4_mul_conj_B
  have h_coeff_c : Complex.normSq ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) = 31 - 12*√5 := normSq_A_w3_z4

  have h_f_le_max : Complex.normSq (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)) ≤
      3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = (4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4 by rfl, show B = ζ₅^4 - 1 by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]
    -- f(c) = (31 - 12√5) + c*(6√5 - 15) + c²*(5 - √5)/2
    -- This is a parabola opening upward with vertex in the interval
    -- We verify directly that f(c) ≤ 3 + φ for all c in [2-√5, 1]
    unfold φ goldenRatio
    nlinarith [h_sqrt5_sq, hc_lo, hc_hi, sq_nonneg c, sq_nonneg (c - 1),
               sq_nonneg (c - (2 - √5)), Real.sqrt_nonneg 5]

  exact h_f_le_max

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
  rw [conj_B4]
  -- A * conj(B) = (-4 + 4ζ₅ - 2ζ₅² + ζ₅⁴)(1 - ζ₅⁴)
  have h_expand : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4) =
      -4 + 4*ζ₅^4 + 4*ζ₅ - 4*ζ₅^5 - 2*ζ₅^2 + 2*ζ₅^6 + ζ₅^4 - ζ₅^8 := by ring
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  have h6 : ζ₅^6 = ζ₅ := by rw [show (6 : ℕ) = 5 + 1 by rfl, pow_add, h5, one_mul, pow_one]
  have h8 : ζ₅^8 = ζ₅^3 := by rw [show (8 : ℕ) = 5 + 3 by rfl, pow_add, h5, one_mul]
  -- Simplify: -4 + 5ζ₅⁴ + 4ζ₅ - 4 - 2ζ₅² + 2ζ₅ - ζ₅³ = -8 + 6ζ₅ - 2ζ₅² - ζ₅³ + 5ζ₅⁴
  have h_simple : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4) = -8 + 6*ζ₅ - 2*ζ₅^2 - ζ₅^3 + 5*ζ₅^4 := by
    calc ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4)
        = -4 + 4*ζ₅^4 + 4*ζ₅ - 4*ζ₅^5 - 2*ζ₅^2 + 2*ζ₅^6 + ζ₅^4 - ζ₅^8 := by ring
      _ = -4 + 4*ζ₅^4 + 4*ζ₅ - 4*1 - 2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 := by rw [h5, h6, h8]
      _ = -8 + 6*ζ₅ - 2*ζ₅^2 - ζ₅^3 + 5*ζ₅^4 := by ring
  rw [h_simple]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re]
  have h8re : (8 : ℂ).re = 8 := rfl
  have h6re : (6 : ℂ).re = 6 := rfl
  have h2re : (2 : ℂ).re = 2 := rfl
  have h5re : (5 : ℂ).re = 5 := rfl
  have h8im : (8 : ℂ).im = 0 := rfl
  have h6im : (6 : ℂ).im = 0 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  have h5im : (5 : ℂ).im = 0 := rfl
  simp only [h8re, h6re, h2re, h5re, h6im, h2im, h5im, sub_zero, zero_mul]
  rw [zeta5_re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

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

/-- The correct vertex is (65 - 15√5)/20 ≈ 1.575 > 1
    So the vertex is ABOVE the interval [2-√5, 1]
    This means the parabola is monotonically DECREASING on [2-√5, 1]
    and achieves its maximum at c = 2-√5 (lower bound) -/
lemma w3_z5_vertex_above_interval : (65 - 15*√5) / 20 > 1 := by
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- Need: (65 - 15√5)/20 > 1 ⟺ 65 - 15√5 > 20 ⟺ 45 > 15√5 ⟺ 3 > √5 ⟺ 9 > 5 ✓
  nlinarith [h_sqrt5_sq]

/-- At c = 1: A + B = (-4 + 4ζ₅ - 2ζ₅² + ζ₅⁴) + (1 - ζ₅) = -3 + 3ζ₅ - 2ζ₅² + ζ₅⁴ -/
lemma w3_z5_at_one_expr : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (1 : ℂ) * (1 - ζ₅) =
    -3 + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4 := by ring

/-- Re(-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴) = (6√5 - 14)/4 = (3√5 - 7)/2
    Calculation: -3 + 3*(√5-1)/4 + 2*(√5+1)/4 + (√5-1)/4 = (6√5 - 14)/4 -/
lemma w3_z5_at_one_re : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (6*√5 - 14) / 4 := by
  have h1 : ζ₅.re = (√5 - 1) / 4 := zeta5_re
  have h2 : (ζ₅^2).re = -(√5 + 1) / 4 := zeta5_sq_re
  have h3 : (ζ₅^4).re = (√5 - 1) / 4 := zeta5_pow4_re
  have h4 : ζ₅.im = Real.sin (2 * π / 5) := zeta5_im_eq_sin
  have h5 : (ζ₅^2).im = Real.sin (π / 5) := zeta5_sq_im_eq
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, h1, h2, h3, h4, h5]
  norm_num
  ring

/-- Im(-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴) = 3*sin(2π/5) - 2*sin(π/5) - sin(2π/5) = 2*sin(2π/5) - 2*sin(π/5) -/
lemma w3_z5_at_one_im : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).im =
    2 * Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) := by
  have h1 : ζ₅.re = (√5 - 1) / 4 := zeta5_re
  have h2 : (ζ₅^2).re = -(√5 + 1) / 4 := zeta5_sq_re
  have h3 : ζ₅.im = Real.sin (2 * π / 5) := zeta5_im_eq_sin
  have h4 : (ζ₅^2).im = Real.sin (π / 5) := zeta5_sq_im_eq
  have h5 : (ζ₅^4).im = -Real.sin (2 * π / 5) := zeta5_pow4_im
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im, h1, h2, h3, h4, h5]
  norm_num
  ring

/-- ||-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴||² at c=1
    Using sin(2π/5) = sin(π/5)*(1+√5)/2:
      2*sin(2π/5) - 2*sin(π/5) = 2*sin(π/5)*((1+√5)/2 - 1) = sin(π/5)*(√5-1)
      Im² = sin²(π/5)*(√5-1)² = ((5-√5)/8)*(6-2√5) = (5-√5)(6-2√5)/8
          = (30 - 10√5 - 6√5 + 2*5)/8 = (40 - 16√5)/8 = 5 - 2√5
    Re = (6√5 - 14)/4
    Re² = (6√5-14)²/16 = (36*5 - 168√5 + 196)/16 = (376 - 168√5)/16 = (94 - 42√5)/4
    Total = (94 - 42√5)/4 + (5 - 2√5) = (94 - 42√5 + 20 - 8√5)/4 = (114 - 50√5)/4
    Need: Total ≤ 3 + φ = 3 + (1+√5)/2 = (7 + √5)/2 = (14 + 2√5)/4
    So need: (114 - 50√5)/4 ≤ (14 + 2√5)/4
    i.e., 114 - 50√5 ≤ 14 + 2√5
    i.e., 100 ≤ 52√5
    i.e., 25 ≤ 13√5
    i.e., 625 ≤ 169*5 = 845 ✓ -/
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
  -- Re² = ((6√5 - 14)/4)² = (376 - 168√5)/16
  have h_re_sq : ((6*√5 - 14) / 4)^2 = (376 - 168*√5) / 16 := by nlinarith [sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (√5 - 1))^2 = Real.sin (π / 5)^2 * (√5 - 1)^2 := by ring
  have h_sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by nlinarith [sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_minus_1_sq]
  unfold φ Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

/-- At c = 2-√5: A + (2-√5)B = (-2-√5) + (2+√5)ζ₅ - 2ζ₅² + ζ₅⁴ -/
lemma w3_z5_at_lower_expr : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + ((2 - √5 : ℝ) : ℂ) * (1 - ζ₅) =
    (-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4 := by
  push_cast
  ring

/-- Re((-2-√5) + (2+√5)ζ₅ - 2ζ₅² + ζ₅⁴) = -1 -/
lemma w3_z5_at_lower_re : ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4).re = -1 := by
  have h : ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4).re =
      (-2 - √5) + (2 + √5) * ζ₅.re - 2 * (ζ₅^2).re + (ζ₅^4).re := by
    have him2 : (2 : ℂ).im = 0 := by norm_num
    have hre2 : (2 : ℂ).re = 2 := by norm_num
    have hcoeff_re : ((2 : ℂ) + (√5 : ℂ)).re = 2 + √5 := by simp [Complex.add_re, Complex.ofReal_re]
    have hcoeff_im : ((2 : ℂ) + (√5 : ℂ)).im = 0 := by simp [Complex.add_im, Complex.ofReal_im]
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      him2, hre2, hcoeff_re, hcoeff_im]
    ring
  rw [h, zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith [h_sqrt5_sq]

/-- Im((-2-√5) + (2+√5)ζ₅ - 2ζ₅² + ζ₅⁴) = sin(π/5)*(1+√5) -/
lemma w3_z5_at_lower_im : ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4).im =
    Real.sin (π / 5) * (1 + √5) := by
  have h : ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4).im =
      (2 + √5) * ζ₅.im - 2 * (ζ₅^2).im + (ζ₅^4).im := by
    have him2 : (2 : ℂ).im = 0 := by norm_num
    have hre2 : (2 : ℂ).re = 2 := by norm_num
    have hcoeff_re : ((2 : ℂ) + (√5 : ℂ)).re = 2 + √5 := by simp [Complex.add_re, Complex.ofReal_re]
    simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_im,
      him2, hre2, hcoeff_re]
    ring
  rw [h, zeta5_im_eq_sin, zeta5_sq_im_eq, zeta5_pow4_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  rw [h_sin_double]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_1_plus_sqrt5_sq : (1 + √5)^2 = 6 + 2*√5 := by nlinarith [h_sqrt5_sq]
  have h_sin_pos : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  -- LHS = (2+√5) * sin(π/5) * (1+√5)/2 - 2*sin(π/5) - sin(π/5)*(1+√5)/2
  -- = sin(π/5) * [(2+√5)*(1+√5)/2 - 2 - (1+√5)/2]
  -- = sin(π/5) * [((2+√5) - 1)*(1+√5)/2 - 2]
  -- = sin(π/5) * [(1+√5)²/2 - 2]
  -- = sin(π/5) * [(6+2√5)/2 - 2]
  -- = sin(π/5) * [3+√5 - 2]
  -- = sin(π/5) * (1+√5)
  nlinarith [h_sqrt5_sq, h_1_plus_sqrt5_sq, h_sin_pos, sq_nonneg (1 + √5)]

/-- |(-2-√5) + (2+√5)ζ₅ - 2ζ₅² + ζ₅⁴|² = 3+φ (equality!) -/
lemma normSq_w3_z5_at_lower : Complex.normSq ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z5_at_lower_re, w3_z5_at_lower_im]
  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  simp only [← sq]
  -- Re² = (-1)² = 1
  -- Im² = sin²(π/5) * (1+√5)² = ((5-√5)/8) * (6+2√5) = (5-√5)(3+√5)/4 = (15+5√5-3√5-5)/4 = (10+2√5)/4 = (5+√5)/2
  -- Total = 1 + (5+√5)/2 = (7+√5)/2 = 3 + (1+√5)/2 = 3 + φ
  have h_im_sq : (Real.sin (π / 5) * (1 + √5))^2 = Real.sin (π / 5)^2 * (1 + √5)^2 := by ring
  have h_1_plus_sqrt5_sq : (1 + √5)^2 = 6 + 2*√5 := by nlinarith [h_sqrt5_sq]
  rw [h_im_sq, h_sin_sq, h_1_plus_sqrt5_sq]
  unfold φ Real.goldenRatio
  nlinarith [h_sqrt5_sq, Real.sqrt_nonneg 5]

set_option maxHeartbeats 800000 in
/-- z5 bound for word3: ‖(-4 + 4*ζ₅ - 2*ζ₅² + ζ₅⁴) + c*(1 - ζ₅)‖ ≤ r_crit for c ∈ [2-√5, 1]

The proof uses:
- f(c) = |A + cB|² is quadratic with vertex at (65 - 15√5)/20 ≈ 1.575 > 1
- Since vertex > 1 and parabola opens upward, f is decreasing on [2-√5, 1]
- Maximum is at c = 2-√5 where f = 3+φ (equality)
- Minimum is at c = 1 where f ≤ 3+φ
- Both endpoints satisfy the bound, hence all c in [2-√5, 1] satisfy it -/
lemma cross_disk_w3_z5_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  set A : ℂ := (-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  -- Value at c = 1
  have h_at_one : ‖A + (1 : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    have h_expr : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (1 : ℂ) * (1 - ζ₅) = -3 + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4 := by ring
    rw [h_expr]
    exact normSq_w3_z5_at_one

  -- Value at c = 2 - √5
  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z5_at_lower_expr]
    exact normSq_w3_z5_at_lower

  have h_normSq_B := normSq_B4
  have h_normSq_A := normSq_A_w3_z5
  have h_re_AB := re_A_w3_z5_mul_conj_B
  have h_vertex := w3_z5_vertex_above_interval

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
  have h_coeff_b : (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re = (7*√5 - 20) / 2 := re_A_w3_z5_mul_conj_B
  have h_coeff_c : Complex.normSq ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) = 46 - 19*√5 := normSq_A_w3_z5

  -- The quadratic f(c) = |A + cB|² has vertex at v = -(Re(A*conj(B))) / |B|²
  -- v = -((7√5-20)/2) / ((5-√5)/2) = (20-7√5)/(5-√5) = (65-15√5)/20
  -- Since v > 1 > c for all c in [2-√5, 1], f is decreasing on [2-√5, 1]
  -- Maximum at c = 2-√5, minimum at c = 1, both satisfy f(c) ≤ 3+φ

  have h_f_le_max : Complex.normSq (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (c : ℂ) * (1 - ζ₅)) ≤ 3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = (-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4 by rfl, show B = 1 - ζ₅ by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    -- f(c) = 46 - 19√5 + 2c*(7√5-20)/2 + c²*(5-√5)/2
    --      = 46 - 19√5 + c*(7√5-20) + c²*(5-√5)/2

    -- Since f is decreasing on [2-√5, 1] and both endpoints satisfy f ≤ 3+φ,
    -- we show f(c) ≤ max(f(2-√5), f(1)) ≤ 3+φ
    -- Actually since f is decreasing: f(c) ≤ f(2-√5) ≤ 3+φ for all c ≥ 2-√5

    -- Use h_at_lower: f(2-√5) ≤ 3+φ and monotonicity
    have h_f_mono : ∀ c₁ c₂ : ℝ, c₁ ≤ c₂ → c₂ ≤ 1 →
        46 - 19*√5 + 2 * c₂ * ((7*√5 - 20) / 2) + c₂^2 * ((5 - √5) / 2) ≤
        46 - 19*√5 + 2 * c₁ * ((7*√5 - 20) / 2) + c₁^2 * ((5 - √5) / 2) := by
      intro c₁ c₂ hc12 hc2_le1
      have h_diff : (46 - 19*√5 + 2 * c₂ * ((7*√5 - 20) / 2) + c₂^2 * ((5 - √5) / 2)) -
                    (46 - 19*√5 + 2 * c₁ * ((7*√5 - 20) / 2) + c₁^2 * ((5 - √5) / 2)) =
                    (c₂ - c₁) * ((7*√5 - 20) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
      -- Need: (c₂ - c₁) * ((7√5-20) + (c₁+c₂)*(5-√5)/2) ≤ 0
      -- Since c₂ ≥ c₁, need: (7√5-20) + (c₁+c₂)*(5-√5)/2 ≤ 0
      -- This holds when c₁+c₂ ≤ 2*(20-7√5)/(5-√5) = 2*(65-15√5)/20 = (65-15√5)/10 ≈ 3.15
      -- Since c₁+c₂ ≤ 2*1 = 2 < 3.15, this should hold
      have h_sum_bound : c₁ + c₂ ≤ 2 := by linarith
      have h_factor_neg : (7*√5 - 20) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
        have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [h_sqrt5_sq]
        -- At c₁+c₂ = 2: (7√5-20) + 2*(5-√5)/2 = 7√5-20 + 5-√5 = 6√5-15 ≈ -1.58 < 0
        calc (7*√5 - 20) + (c₁ + c₂) * ((5 - √5) / 2)
            ≤ (7*√5 - 20) + 2 * ((5 - √5) / 2) := by gcongr
          _ = 6*√5 - 15 := by ring
          _ ≤ 0 := by nlinarith [h_sqrt5_sq]
      nlinarith [hc12, h_factor_neg]

    calc 46 - 19*√5 + 2 * c * ((7*√5 - 20) / 2) + c^2 * ((5 - √5) / 2)
        ≤ 46 - 19*√5 + 2 * (2 - √5) * ((7*√5 - 20) / 2) + (2 - √5)^2 * ((5 - √5) / 2) := by
          apply h_f_mono (2 - √5) c (by linarith [hc_lo]) hc_hi
      _ ≤ 3 + φ := by
          have h_eq : 46 - 19*√5 + 2 * (2 - √5) * ((7*√5 - 20) / 2) + (2 - √5)^2 * ((5 - √5) / 2) =
                      Complex.normSq ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4) := by
            rw [Complex.normSq_apply, w3_z5_at_lower_re, w3_z5_at_lower_im]
            simp only [← sq]
            have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
            have h_im_sq : (Real.sin (π / 5) * (1 + √5))^2 = Real.sin (π / 5)^2 * (1 + √5)^2 := by ring
            have h_1_plus_sqrt5_sq : (1 + √5)^2 = 6 + 2*√5 := by nlinarith [h_sqrt5_sq]
            rw [h_im_sq, h_sin_sq, h_1_plus_sqrt5_sq]
            nlinarith [h_sqrt5_sq]
          rw [h_eq]
          exact normSq_w3_z5_at_lower

  exact h_f_le_max

end TDCSG.CompoundSymmetry.GG5
