/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.Zeta5
import Mathlib.Analysis.Convex.Mul

/-!
# Basic Cross-Disk Bounds

This file establishes fundamental norm bounds for complex expressions involving roots of unity,
proving that certain intermediate points in word computations remain within disk boundaries.

## Main results

- `normSq_at_neg1`: Norm bound at the lower interval endpoint
- `normSq_at_upper_endpoint`: Norm bound at the upper interval endpoint
- `vertex_lt_neg1`: The parabola vertex lies below -1

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (segmentPoint psi E E' ζ₅ zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

lemma zeta5_cubed_minus_fourth_ne_zero : ζ₅^3 - ζ₅^4 ≠ 0 := by
  intro h
  have heq : ζ₅^3 = ζ₅^4 := sub_eq_zero.mp h
  have hζ_ne : ζ₅ ≠ 0 := zeta5_ne_zero
  have h3_ne : ζ₅^3 ≠ 0 := pow_ne_zero 3 hζ_ne
  have h1 : ζ₅ = 1 := by
    have hdiv : ζ₅^4 / ζ₅^3 = 1 := by rw [← heq]; exact div_self h3_ne
    grind
  exact zeta5_ne_one h1

lemma endpoint_neg1_re : (-2 + ζ₅^2 - ζ₅^3 + ζ₅^4).re = (√5 - 9) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  have h2 : (2 : ℂ).re = 2 := by simp
  rw [h2, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma endpoint_neg1_im : (-2 + ζ₅^2 - ζ₅^3 + ζ₅^4).im =
    2 * Real.sin (π / 5) - Real.sin (2 * π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im]
  have h2 : (2 : ℂ).im = 0 := by simp
  rw [h2, neg_zero, zeta5_sq_im_eq, zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

lemma normSq_at_neg1 : ‖(-2 : ℂ) + ζ₅^2 - ζ₅^3 + ζ₅^4‖^2 ≤ 3 + φ := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [endpoint_neg1_re, endpoint_neg1_im]
  have h_cos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have h_sin_double : Real.sin (2 * π / 5) = 2 * Real.sin (π / 5) * Real.cos (π / 5) := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
  rw [h_sin_double]
  have h_factor : 2 * Real.sin (π / 5) - 2 * Real.sin (π / 5) * Real.cos (π / 5) =
                  2 * Real.sin (π / 5) * (1 - Real.cos (π / 5)) := by ring
  rw [h_factor, h_cos]
  have h_1_minus : 1 - (1 + √5) / 4 = (3 - √5) / 4 := by ring
  rw [h_1_minus]
  have h_sin_sq : Real.sin (π / 5) ^ 2 = 1 - ((1 + √5) / 4) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (π / 5)
    rw [h_cos] at h; linarith
  simp only [← sq]
  have h_im_sq : (2 * Real.sin (π / 5) * ((3 - √5) / 4)) ^ 2 =
                 Real.sin (π / 5) ^ 2 * (3 - √5)^2 / 4 := by ring
  rw [h_im_sq, h_sin_sq]
  unfold φ  Real.goldenRatio
  nlinarith [Real.sqrt_nonneg 5, sqrt5_sq, sq_nonneg (Real.sin (π / 5)), sq_nonneg ((3 - √5) / 4), sq_nonneg ((√5 - 9) / 4)]

lemma zeta5_sq_im' : (ζ₅^2).im = Real.sin (π / 5) := by
  rw [zeta5_sq_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
             Complex.I_im, Complex.I_re, Complex.ofReal_re]
  have h : Real.sin (4 * π / 5) = Real.sin (π / 5) := by
    rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.sin_pi_sub]
  linarith [h]

lemma zeta5_cubed_im' : (ζ₅^3).im = -Real.sin (π / 5) := by
  rw [zeta5_cubed_eq, Complex.exp_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
             Complex.cos_ofReal_im, Complex.sin_ofReal_re, mul_zero, mul_one, zero_add]
  rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring, Real.sin_add_pi]
  ring

lemma zeta5_pow4_im' : (ζ₅^4).im = -Real.sin (2 * π / 5) := by
  have : ζ₅^4 = starRingEnd ℂ ζ₅ := by rw [← zeta5_conj]
  rw [this, Complex.conj_im, zeta5_im_eq_sin]

lemma B_re' : (ζ₅^3 - ζ₅^4).re = -√5 / 2 := by
  simp only [Complex.sub_re]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma B_im : (ζ₅^3 - ζ₅^4).im = Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  simp only [Complex.sub_im]
  rw [zeta5_cubed_im', zeta5_pow4_im']
  ring

lemma normSq_B : Complex.normSq (ζ₅^3 - ζ₅^4) = (5 - √5) / 2 := by
  rw [Complex.normSq_apply]
  simp only [← sq]
  rw [B_re', B_im]
  have h_sin_double : Real.sin (2 * π / 5) = 2 * Real.sin (π / 5) * Real.cos (π / 5) := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
  have h_cos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have h_sin_sq := sin_sq_pi_div_5
  rw [h_sin_double, h_cos]
  have h1 : 2 * Real.sin (π / 5) * ((1 + √5) / 4) - Real.sin (π / 5) =
            Real.sin (π / 5) * (√5 - 1) / 2 := by ring
  rw [h1]
  have h2 : (-√5 / 2)^2 = 5 / 4 := by nlinarith [sqrt5_sq]
  have h3 : (Real.sin (π / 5) * (√5 - 1) / 2)^2 =
            Real.sin (π / 5)^2 * (√5 - 1)^2 / 4 := by ring
  rw [h2, h3, h_sin_sq, sqrt5_minus_one_sq]
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

lemma re_A_mul_conj_B :
    (((-2 : ℂ) + ζ₅^2) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re = 3 * √5 / 2 := by
  have h_conj_B : starRingEnd ℂ (ζ₅^3 - ζ₅^4) = ζ₅^2 - ζ₅ := by
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
  rw [h_conj_B]
  have h_expand : ((-2 : ℂ) + ζ₅^2) * (ζ₅^2 - ζ₅) = -2*ζ₅^2 + 2*ζ₅ + ζ₅^4 - ζ₅^3 := by ring
  rw [h_expand]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
  have h2re : (2 : ℂ).re = 2 := by simp
  have h2im : (2 : ℂ).im = 0 := by simp
  have hneg2im : (-2 : ℂ).im = 0 := by simp
  simp only [h2re, h2im, hneg2im, sub_zero, zero_mul]
  rw [zeta5_sq_re, zeta5_re, zeta5_pow4_re, zeta5_cubed_re]
  ring

lemma vertex_lt_neg1 : -(3 * √5 / 2) / ((5 - √5) / 2) < -1 := by
  have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  have h_sqrt25 : √25 = 5 := by
    rw [show (25 : ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
  have h_5_minus_sqrt5_pos : 0 < 5 - √5 := by
    have : √5 < 5 := by
      calc √5 < √25 := Real.sqrt_lt_sqrt (by linarith) (by norm_num)
        _ = 5 := h_sqrt25
    linarith
  have h_denom_pos : 0 < (5 - √5) / 2 := by linarith
  have h_simp : -(3 * √5 / 2) / ((5 - √5) / 2) = -(3 * √5) / (5 - √5) := by field_simp
  rw [h_simp]
  have h_4sqrt5_gt_5 : 4 * √5 > 5 := by
    have h_sq : (4 * √5)^2 = 80 := by
      calc (4 * √5)^2 = 16 * √5^2 := by ring
        _ = 16 * 5 := by simp only [sqrt5_sq]
        _ = 80 := by ring
    have h4sqrt5_pos : 0 < 4 * √5 := by linarith
    have h_sqrt80 : √80 = 4 * √5 := by
      rw [← h_sq, Real.sqrt_sq (le_of_lt h4sqrt5_pos)]
    calc 4 * √5 = √80 := h_sqrt80.symm
      _ > √25 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 5 := h_sqrt25
  have h_3sqrt5_gt : 3 * √5 > 5 - √5 := by linarith
  rw [neg_div, neg_lt_neg_iff]
  rw [one_lt_div h_5_minus_sqrt5_pos]
  linarith

/-- The norm square of A + t*B expands as a quadratic in t. -/
lemma normSq_add_ofReal_mul (A B : ℂ) (t : ℝ) :
    Complex.normSq (A + (t : ℂ) * B) =
    Complex.normSq A + 2 * t * (A * starRingEnd ℂ B).re + t^2 * Complex.normSq B := by
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

lemma normSq_at_upper_endpoint :
    Complex.normSq ((-2 : ℂ) + ζ₅^2 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4)) = 3 + φ := by
  have h_sin_sq := sin_sq_pi_div_5
  have h_sq := sqrt5_minus_one_sq

  rw [Complex.normSq_apply]
  simp only [← sq]

  have h_re : ((-2 : ℂ) + ζ₅^2 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4)).re = (-2 - √5) / 2 := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               Complex.sub_re, Complex.neg_re]
    rw [zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
    have h2re : (2 : ℂ).re = 2 := by simp
    rw [h2re]
    ring_nf
    nlinarith [sqrt5_sq]

  have h_im : ((-2 : ℂ) + ζ₅^2 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4)).im =
              Real.sin (π / 5) * (√5 - 1) / 2 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
               Complex.sub_im, Complex.neg_im]
    have h2im : (2 : ℂ).im = 0 := by simp
    rw [h2im, zeta5_sq_im', zeta5_cubed_im', zeta5_pow4_im', B_re']
    have h_sin_double : Real.sin (2 * π / 5) = 2 * Real.sin (π / 5) * Real.cos (π / 5) := by
      rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    have h_cos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
    rw [h_sin_double, h_cos]
    have h1 : (1 - √5) * (√5 - 1) = -(√5 - 1)^2 := by ring
    grind

  rw [h_re, h_im]
  calc ((-2 - √5) / 2)^2 + (Real.sin (π / 5) * (√5 - 1) / 2)^2
      = (4 + 4*√5 + √5^2) / 4 + Real.sin (π / 5)^2 * (√5 - 1)^2 / 4 := by ring
    _ = (4 + 4*√5 + 5) / 4 + ((5 - √5) / 8) * (6 - 2*√5) / 4 := by rw [sqrt5_sq, h_sin_sq, h_sq]
    _ = (7 + √5) / 2 := by nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
    _ = 3 + φ := by unfold φ Real.goldenRatio; ring

end TDCSG.CompoundSymmetry.GG5
