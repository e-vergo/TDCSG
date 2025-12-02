/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.CrossDiskRestricted

/-!
# Helper Lemmas for Word 3 Cross-Disk Bounds

This file contains detailed algebraic computations supporting the word3 cross-disk bounds,
including real/imaginary part calculations and norm square evaluations for multiple intermediate
steps.

## Main results

- `normSq_w3_z1_at_lower`: Norm bound at lower endpoint for z1
- `normSq_w3_z2_at_lower`: Norm bound at lower endpoint for z2
- `normSq_w3_z3_at_lower`: Norm bound at lower endpoint for z3
- `normSq_w3_z5_at_lower`: Norm bound at lower endpoint for z5

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (segment_length translation_length_1 translation_length_2 segmentPoint psi t_F E E' F G ζ₅ zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

private noncomputable abbrev c_lower_word3 : ℝ := 2 - √5

lemma A_w3_z1_re : (ζ₅^4 - 2 : ℂ).re = (√5 - 9) / 4 := by
  simp only [Complex.sub_re]
  have h2re : (2 : ℂ).re = 2 := by rfl
  rw [h2re, zeta5_pow4_re]
  ring

lemma A_w3_z1_im : (ζ₅^4 - 2 : ℂ).im = -Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im]
  have h2im : (2 : ℂ).im = 0 := by rfl
  rw [h2im, zeta5_pow4_im']
  ring

lemma normSq_A_w3_z1 : Complex.normSq (ζ₅^4 - 2) = 6 - √5 := by
  rw [Complex.normSq_apply, A_w3_z1_re, A_w3_z1_im]
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  simp only [← sq]
  have h_re_sq : ((√5 - 9) / 4)^2 = (86 - 18*√5) / 16 := by grind
  have h_neg_sq : (-Real.sin (2 * π / 5))^2 = Real.sin (2 * π / 5)^2 := by ring
  grind

lemma re_A_w3_z1_mul_conj_B :
    ((ζ₅^4 - 2 : ℂ) * starRingEnd ℂ (1 - ζ₅)).re = (2*√5 - 5) / 2 := by
  rw [conj_one_sub_zeta5]
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

lemma w3_z1_vertex : -(((2*√5 - 5) / 2) / ((5 - √5) / 2)) = (3 - √5) / 4 := by
  have h_5_minus_sqrt5_ne : 5 - √5 ≠ 0 := by nlinarith [Real.sqrt_nonneg 5, sqrt5_sq]
  field_simp
  nlinarith [sqrt5_sq]

lemma w3_z1_vertex_in_interval : (2 - √5) < (3 - √5) / 4 ∧ (3 - √5) / 4 < 1 := by
  constructor <;> nlinarith [Real.sqrt_nonneg 5, sqrt5_sq]

lemma w3_z1_at_one_re : (ζ₅^4 - ζ₅ - 1 : ℂ).re = -1 := by
  simp only [Complex.sub_re, Complex.one_re]
  rw [zeta5_pow4_re, zeta5_re]
  ring

lemma w3_z1_at_one_im : (ζ₅^4 - ζ₅ - 1 : ℂ).im = -2 * Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im, Complex.one_im]
  rw [zeta5_pow4_im', zeta5_im_eq_sin]
  ring

lemma normSq_w3_z1_at_one : Complex.normSq (ζ₅^4 - ζ₅ - 1) = 3 + φ := by
  rw [Complex.normSq_apply, w3_z1_at_one_re, w3_z1_at_one_im]
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  simp only [← sq]
  calc (-1)^2 + (-2 * Real.sin (2 * π / 5))^2
      = 1 + 4 * Real.sin (2 * π / 5)^2 := by ring
    _ = 1 + 4 * ((5 + √5) / 8) := by rw [h_sin_sq]
    _ = 1 + (5 + √5) / 2 := by ring
    _ = (7 + √5) / 2 := by ring
    _ = 3 + (1 + √5) / 2 := by ring
    _ = 3 + φ := by unfold φ Real.goldenRatio; ring

lemma w3_z1_at_lower_re : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ).re = 3 * (1 - √5) / 2 := by
  have h_expr : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ) = ζ₅^4 - ((2 - √5 : ℝ) : ℂ) * ζ₅ - (√5 : ℂ) := by
    push_cast; ring
  rw [h_expr]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul]
  rw [zeta5_pow4_re, zeta5_re]
  nlinarith [sqrt5_sq]

lemma w3_z1_at_lower_im : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ).im = -(3 - √5) * Real.sin (2 * π / 5) := by
  have h_expr : (ζ₅^4 - (2 - √5)*ζ₅ - √5 : ℂ) = ζ₅^4 - ((2 - √5 : ℝ) : ℂ) * ζ₅ - (√5 : ℂ) := by
    push_cast; ring
  rw [h_expr]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [zeta5_pow4_im', zeta5_im_eq_sin]
  ring

lemma normSq_w3_z1_at_lower : Complex.normSq (ζ₅^4 - (2 - √5)*ζ₅ - √5) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z1_at_lower_re, w3_z1_at_lower_im]
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  simp only [← sq]
  unfold φ Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5, h_sin_sq, sq_nonneg (Real.sin (2 * π / 5))]

lemma A_w3_z2_re : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4).re = (9 - 3*√5) / 4 := by
  have h2re : (2 : ℂ).re = 2 := rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, h2re]
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [h2im, zero_mul, sub_zero]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma A_w3_z2_im : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4).im = 2 * Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  have h2im : (2 : ℂ).im = 0 := rfl
  have h2re : (2 : ℂ).re = 2 := rfl
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, h2im, h2re, zero_mul, add_zero]
  rw [zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

lemma normSq_A_w3_z2 : Complex.normSq ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) = 11 - 4*√5 := by
  rw [Complex.normSq_apply, A_w3_z2_re, A_w3_z2_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : 2 * Real.sin (2 * π / 5) - Real.sin (π / 5) = Real.sin (π / 5) * √5 := by grind
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((9 - 3*√5) / 4)^2 = (126 - 54*√5) / 16 := by grind
  have h_im_sq : (Real.sin (π / 5) * √5)^2 = Real.sin (π / 5)^2 * 5 := by grind
  grind

lemma conj_B3 : starRingEnd ℂ (ζ₅^4 - 1) = ζ₅ - 1 := by
  simp only [map_sub, map_one, map_pow, zeta5_conj]
  calc (ζ₅^4)^4 - 1 = ζ₅^16 - 1 := by ring
    _ = ζ₅^(16 % 5) - 1 := by rw [zeta5_pow_reduce 16]
    _ = ζ₅ - 1 := by norm_num

lemma re_A_w3_z2_mul_conj_B :
    (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re = (3*√5 - 10) / 2 := by
  rw [conj_B3]
  have h_expand : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * (ζ₅ - 1) = 2*ζ₅ - 4 + 3*ζ₅^4 - ζ₅^3 := by
    calc ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * (ζ₅ - 1)
        = 2*ζ₅ - 2 + ζ₅^4 - ζ₅^3 - 2*ζ₅^5 + 2*ζ₅^4 := by ring
      _ = 2*ζ₅ - 2 + ζ₅^4 - ζ₅^3 - 2*1 + 2*ζ₅^4 := by simp only [zeta5_pow_five_C]
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

lemma w3_z2_vertex : -(((3*√5 - 10) / 2) / ((5 - √5) / 2)) = (7 - √5) / 4 := by
  have h_5_minus_sqrt5_ne : 5 - √5 ≠ 0 := by nlinarith [Real.sqrt_nonneg 5, sqrt5_sq]
  have h_denom_ne : (5 - √5) / 2 ≠ 0 := by grind
  grind

lemma w3_z2_vertex_above_interval : (7 - √5) / 4 > 1 := by
  nlinarith [sqrt5_sq]

lemma w3_z2_at_one_expr : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (1 : ℂ) * (ζ₅^4 - 1) = 1 + ζ₅^3 - ζ₅^4 := by
  ring

lemma w3_z2_at_one_re : ((1 : ℂ) + ζ₅^3 - ζ₅^4).re = (2 - √5) / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma w3_z2_at_one_im : ((1 : ℂ) + ζ₅^3 - ζ₅^4).im = Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.one_im]
  rw [zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

lemma normSq_w3_z2_at_one : Complex.normSq ((1 : ℂ) + ζ₅^3 - ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z2_at_one_re, w3_z2_at_one_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : Real.sin (2 * π / 5) - Real.sin (π / 5) =
      Real.sin (π / 5) * (√5 - 1) / 2 := by grind
  simp only [← sq]
  rw [h_im_simp]
  unfold φ Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5, h_sin_sq, sq_nonneg (Real.sin (π / 5))]

lemma w3_z2_at_lower_expr : ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + ((2 - √5 : ℝ) : ℂ) * (ζ₅^4 - 1) =
    (√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4 := by
  push_cast
  ring

lemma w3_z2_at_lower_re : ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4).re = (2*√5 - 3) / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  nlinarith [sqrt5_sq]

lemma w3_z2_at_lower_im : ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4).im =
    √5 * Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

lemma normSq_w3_z2_at_lower : Complex.normSq ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z2_at_lower_re, w3_z2_at_lower_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : √5 * Real.sin (2 * π / 5) - Real.sin (π / 5) =
      Real.sin (π / 5) * (√5 + 3) / 2 := by
    rw [h_sin_double]
    have h1 : √5 * (1 + √5) = √5 + 5 := by grind
    grind
  simp only [← sq]
  rw [h_im_simp]
  unfold φ Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5, h_sin_sq, sq_nonneg (Real.sin (π / 5))]

lemma A_w3_z3_re : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4).re = (3*√5 - 9) / 4 := by
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
             h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma A_w3_z3_im : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4).im =
    3 * Real.sin (π / 5) - 2 * Real.sin (2 * π / 5) := by
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
             h2re, h2im, zero_mul, add_zero]
  rw [zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im']
  ring

lemma normSq_A_w3_z3 : Complex.normSq ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) = 16 - 7*√5 := by
  rw [Complex.normSq_apply, A_w3_z3_re, A_w3_z3_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : 3 * Real.sin (π / 5) - 2 * Real.sin (2 * π / 5) =
      Real.sin (π / 5) * (2 - √5) := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5, h_sin_sq, sq_nonneg (Real.sin (π / 5))]

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

lemma re_A_w3_z3_mul_conj_B :
    (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re = (5*√5 - 10) / 2 := by
  rw [conj_B_z3]
  have h_expand : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * (ζ₅^2 - ζ₅) =
      -4 + 4*ζ₅ - 2*ζ₅^2 - ζ₅^3 + 3*ζ₅^4 := by
    calc ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * (ζ₅^2 - ζ₅)
        = -2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 - 2*ζ₅^5 + 2*ζ₅^4 + 2*ζ₅^6 - 2*ζ₅^5 := by ring
      _ = -2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 - 2*1 + 2*ζ₅^4 + 2*ζ₅ - 2*1 := by simp only [zeta5_pow_five_C, zeta5_pow_six]
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

lemma w3_z3_vertex_below_interval : (5 - 3*√5) / 4 < 2 - √5 := by
  nlinarith [sqrt5_sq]

lemma w3_z3_at_one_expr : ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (1 : ℂ) * (ζ₅^3 - ζ₅^4) =
    -2 + ζ₅^2 - ζ₅^3 + ζ₅^4 := by ring

lemma w3_z3_at_one_re : ((-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4).re = (√5 - 9) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  have h2re : (2 : ℂ).re = 2 := rfl
  rw [h2re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma w3_z3_at_one_im : ((-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4).im =
    2 * Real.sin (π / 5) - Real.sin (2 * π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im]
  have h2im : (2 : ℂ).im = 0 := rfl
  rw [h2im, zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im']
  ring

lemma normSq_w3_z3_at_one : Complex.normSq ((-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z3_at_one_re, w3_z3_at_one_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_im_simp : 2 * Real.sin (π / 5) - Real.sin (2 * π / 5) =
      Real.sin (π / 5) * (3 - √5) / 2 := by
    rw [h_sin_double]
    ring
  simp only [← sq]
  rw [h_im_simp]
  have h_re_sq : ((√5 - 9) / 4)^2 = (86 - 18*√5) / 16 := by grind
  have h_im_sq : (Real.sin (π / 5) * (3 - √5) / 2)^2 =
      Real.sin (π / 5)^2 * (3 - √5)^2 / 4 := by ring
  have h_3_minus_sqrt5_sq : (3 - √5)^2 = 14 - 6*√5 := by grind
  rw [h_re_sq, h_im_sq, h_sin_sq, h_3_minus_sqrt5_sq]
  unfold φ
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5, Real.goldenRatio_pos]

lemma w3_z3_at_lower_expr :
    ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + ((2 - √5 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4) =
    (-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4 := by
  push_cast
  ring

lemma w3_z3_at_lower_re :
    ((-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4).re = (1 - √5) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
             Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h2re : (2 : ℂ).re = 2 := rfl
  rw [h2re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  nlinarith [sqrt5_sq]

lemma w3_z3_at_lower_im :
    ((-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4).im =
    Real.sin (π / 5) * (√5 - 3) / 2 := by
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
             Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have h2im : (2 : ℂ).im = 0 := rfl
  rw [h2im, zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im']
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  rw [h_sin_double]
  set s := Real.sin (π / 5) with hs_def
  have h_factor : s + √5 * s - √5 * (s * (1 + √5) / 2) = s * (√5 - 3) / 2 := by
    have h_expand : √5 * (s * (1 + √5) / 2) = s * √5 * (1 + √5) / 2 := by ring
    rw [h_expand]
    have h_sqrt5_times : √5 * (1 + √5) = √5 + 5 := by grind
    calc s + √5 * s - s * √5 * (1 + √5) / 2
        = s + √5 * s - s * (√5 * (1 + √5)) / 2 := by ring
      _ = s + √5 * s - s * (√5 + 5) / 2 := by rw [h_sqrt5_times]
      _ = s * (√5 - 3) / 2 := by ring
  convert h_factor using 1; ring

lemma normSq_w3_z3_at_lower :
    Complex.normSq ((-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z3_at_lower_re, w3_z3_at_lower_im]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  simp only [← sq]
  have h_re_sq : ((1 - √5) / 4)^2 = (6 - 2*√5) / 16 := by grind
  have h_im_sq : (Real.sin (π / 5) * (√5 - 3) / 2)^2 =
      Real.sin (π / 5)^2 * (√5 - 3)^2 / 4 := by ring
  have h_sqrt5_minus_3_sq : (√5 - 3)^2 = 14 - 6*√5 := by grind
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_minus_3_sq]
  unfold φ
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5, Real.goldenRatio_pos]

lemma A_w3_z4_re : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).re = (19 - 5*√5) / 4 := by
  have h4re : (4 : ℂ).re = 4 := rfl
  have h4im : (4 : ℂ).im = 0 := rfl
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, h4re, h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma A_w3_z4_im : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).im = -Real.sin (π / 5) := by
  have h4im : (4 : ℂ).im = 0 := Complex.ofReal_im 4
  have h2re : (2 : ℂ).re = 2 := Complex.ofReal_re 2
  have h2im : (2 : ℂ).im = 0 := Complex.ofReal_im 2
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
             h2re, h2im, add_zero, zero_mul,
             zeta5_im_eq_sin, zeta5_cubed_im, zeta5_pow4_im, h4im]
  have h_sin6 : Real.sin (6 * π / 5) = -Real.sin (π / 5) := by
    rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring, Real.sin_add_pi]
  rw [h_sin6]
  ring

lemma normSq_A_w3_z4 : Complex.normSq ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) = 31 - 12*√5 := by
  rw [Complex.normSq_apply, A_w3_z4_re, A_w3_z4_im]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  simp only [← sq]
  rw [neg_sq, h_sin_sq]
  nlinarith [sqrt5_sq]

lemma re_A_w3_z4_mul_conj_B : (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re =
    (6*√5 - 15) / 2 := by
  rw [conj_B3]
  have hA_re : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).re = (19 - 5*√5) / 4 := A_w3_z4_re
  have hA_im : ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4).im = -Real.sin (π / 5) := A_w3_z4_im
  have hB_re : (ζ₅ - 1 : ℂ).re = ζ₅.re - 1 := by simp only [Complex.sub_re, Complex.one_re]
  have hB_im : (ζ₅ - 1 : ℂ).im = ζ₅.im := by simp only [Complex.sub_im, Complex.one_im, sub_zero]
  rw [Complex.mul_re, hA_re, hA_im, hB_re, hB_im, zeta5_re, zeta5_im_eq_sin]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  rw [h_sin_double]
  have h_expand : -Real.sin (π / 5) * (Real.sin (π / 5) * (1 + √5) / 2) =
      -Real.sin (π / 5)^2 * (1 + √5) / 2 := by ring
  rw [h_expand, h_sin_sq]
  nlinarith [sqrt5_sq]

lemma A_w3_z5_re : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (7*√5 - 19) / 4 := by
  have h4re : (4 : ℂ).re = 4 := by rfl
  have h4im : (4 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
             h4re, h4im, h2re, h2im]
  rw [zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  ring

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

lemma normSq_A_w3_z5 : Complex.normSq ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) = 46 - 19*√5 := by
  rw [Complex.normSq_apply, A_w3_z5_re, A_w3_z5_im]
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
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

lemma re_A_w3_z5_mul_conj_B :
    (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re = (7*√5 - 20) / 2 := by
  rw [conj_one_sub_zeta5]
  have h_expand : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4) =
      -4 + 4*ζ₅^4 + 4*ζ₅ - 4*ζ₅^5 - 2*ζ₅^2 + 2*ζ₅^6 + ζ₅^4 - ζ₅^8 := by ring
  have h_simple : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4) = -8 + 6*ζ₅ - 2*ζ₅^2 - ζ₅^3 + 5*ζ₅^4 := by
    calc ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4)
        = -4 + 4*ζ₅^4 + 4*ζ₅ - 4*ζ₅^5 - 2*ζ₅^2 + 2*ζ₅^6 + ζ₅^4 - ζ₅^8 := by ring
      _ = -4 + 4*ζ₅^4 + 4*ζ₅ - 4*1 - 2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 := by simp only [zeta5_pow_five_C, zeta5_pow_six, zeta5_pow_eight]
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

lemma w3_z5_vertex_above_interval : (65 - 15*√5) / 20 > 1 := by
  nlinarith [sqrt5_sq]

lemma w3_z5_at_one_re : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (6*√5 - 14) / 4 := by
  have h1 : ζ₅.re = (√5 - 1) / 4 := zeta5_re
  have h2 : (ζ₅^2).re = -(√5 + 1) / 4 := zeta5_sq_re
  have h3 : (ζ₅^4).re = (√5 - 1) / 4 := zeta5_pow4_re
  have h4 : ζ₅.im = Real.sin (2 * π / 5) := zeta5_im_eq_sin
  have h5 : (ζ₅^2).im = Real.sin (π / 5) := zeta5_sq_im_eq
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, h1, h2, h3, h4, h5]
  norm_num
  ring

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
  have h_re_sq : ((6*√5 - 14) / 4)^2 = (376 - 168*√5) / 16 := by nlinarith [sqrt5_sq]
  have h_im_sq : (Real.sin (π / 5) * (√5 - 1))^2 = Real.sin (π / 5)^2 * (√5 - 1)^2 := by ring
  have h_sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by nlinarith [sqrt5_sq]
  rw [h_re_sq, h_im_sq, h_sin_sq, h_sqrt5_minus_1_sq]
  unfold φ Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

lemma w3_z5_at_lower_expr : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + ((2 - √5 : ℝ) : ℂ) * (1 - ζ₅) =
    (-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4 := by
  push_cast
  ring

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
  nlinarith [sqrt5_sq]

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
  have h_1_plus_sqrt5_sq : (1 + √5)^2 = 6 + 2*√5 := by grind
  have h_sin_pos : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  nlinarith [sqrt5_sq, h_1_plus_sqrt5_sq, h_sin_pos, sq_nonneg (1 + √5)]

lemma normSq_w3_z5_at_lower : Complex.normSq ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4) ≤ 3 + φ := by
  rw [Complex.normSq_apply, w3_z5_at_lower_re, w3_z5_at_lower_im]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  simp only [← sq]
  have h_im_sq : (Real.sin (π / 5) * (1 + √5))^2 = Real.sin (π / 5)^2 * (1 + √5)^2 := by ring
  have h_1_plus_sqrt5_sq : (1 + √5)^2 = 6 + 2*√5 := by grind
  rw [h_im_sq, h_sin_sq, h_1_plus_sqrt5_sq]
  unfold φ  Real.goldenRatio
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

end TDCSG.CompoundSymmetry.GG5
