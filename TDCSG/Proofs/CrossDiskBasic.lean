/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.Zeta5
import Mathlib.Analysis.Convex.Mul

/-!
# Basic Lemmas for Cross-Disk Analysis in GG(5,5)

This file contains the foundational lemmas used in cross-disk membership bounds
for GG(5,5), including:
- Algebraic properties of the fifth roots of unity
- Endpoint norm calculations at c = -1 and c = (1-sqrt5)/2
- Helper lemmas for trigonometric identities and complex number calculations
- Properties of the vectors A = -2 + zeta5^2 and B = zeta5^3 - zeta5^4

These lemmas are shared across multiple proofs and extracted here for reusability.
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real TDCSG.Definitions

/-! ### B != 0 lemma -/

/-- zeta5^3 - zeta5^4 != 0 since distinct primitive roots are distinct. -/
lemma zeta5_cubed_minus_fourth_ne_zero : ζ₅^3 - ζ₅^4 ≠ 0 := by
  intro h
  have heq : ζ₅^3 = ζ₅^4 := sub_eq_zero.mp h
  have hζ_ne : ζ₅ ≠ 0 := zeta5_ne_zero
  have h3_ne : ζ₅^3 ≠ 0 := pow_ne_zero 3 hζ_ne
  have h1 : ζ₅ = 1 := by
    have hdiv : ζ₅^4 / ζ₅^3 = 1 := by rw [← heq]; exact div_self h3_ne
    grind
  exact zeta5_ne_one h1

/-! ### Endpoint norm bounds -/

/-- Real part of -2 + zeta5^2 - zeta5^3 + zeta5^4 equals (sqrt5 - 9)/4 -/
lemma endpoint_neg1_re : (-2 + ζ₅^2 - ζ₅^3 + ζ₅^4).re = (√5 - 9) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  have h2 : (2 : ℂ).re = 2 := by simp
  rw [h2, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Imaginary part of -2 + zeta5^2 - zeta5^3 + zeta5^4 -/
lemma endpoint_neg1_im : (-2 + ζ₅^2 - ζ₅^3 + ζ₅^4).im =
    2 * Real.sin (π / 5) - Real.sin (2 * π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im]
  have h2 : (2 : ℂ).im = 0 := by simp
  rw [h2, neg_zero, zeta5_sq_im_eq, zeta5_cubed_im_eq, zeta5_pow4_im]
  ring

/-! ### Main norm bound at c = -1

The key calculation is: ||-2 + zeta5^2 - zeta5^3 + zeta5^4||^2 <= 3 + phi

re = (sqrt5 - 9)/4, im = 2sin(pi/5) - sin(2pi/5)

Using sin(2pi/5) = 2sin(pi/5)cos(pi/5) and cos(pi/5) = (1+sqrt5)/4:
im = 2sin(pi/5)(1 - (1+sqrt5)/4) = 2sin(pi/5)(3-sqrt5)/4 = sin(pi/5)(3-sqrt5)/2

So normSq = ((sqrt5-9)/4)^2 + (sin(pi/5)(3-sqrt5)/2)^2

Using sin^2(pi/5) = 1 - cos^2(pi/5) = 1 - ((1+sqrt5)/4)^2 = (5-sqrt5)/8:

normSq = (86 - 18sqrt5)/16 + (5-sqrt5)/8 * (3-sqrt5)^2/4
       = (34 - 10sqrt5)/4

We need (34 - 10sqrt5)/4 <= 3 + phi = (14+2sqrt5)/4
<=> 34 - 10sqrt5 <= 14 + 2sqrt5
<=> 20 <= 12sqrt5
<=> 5/3 <= sqrt5 (since sqrt5 ~ 2.236 > 1.67)
-/

/-- The normSq at c = -1: ||-2 + zeta5^2 - zeta5^3 + zeta5^4||^2 <= 3 + phi -/
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
  unfold φ Real.goldenRatio
  have h1 : ((√5 - 9) / 4) ^ 2 = (√5^2 - 18 * √5 + 81) / 16 := by ring
  have h2 : 1 - ((1 + √5) / 4) ^ 2 = (16 - (1 + √5)^2) / 16 := by ring
  have h3 : (1 + √5)^2 = 1 + 2*√5 + √5^2 := by ring
  have h4 : (3 - √5)^2 = 9 - 6*√5 + √5^2 := by ring
  rw [h1, h2, h3, h4]
  have h_sqrt5_bound : (5 / 3 : ℝ) < √5 := by
    have h25_9 : (25 / 9 : ℝ) < 5 := by norm_num
    have h53_pos : (0 : ℝ) ≤ 5 / 3 := by norm_num
    calc 5 / 3 = √((5/3)^2) := by rw [Real.sqrt_sq h53_pos]
         _ = √(25/9) := by ring_nf
         _ < √5 := Real.sqrt_lt_sqrt (by norm_num) h25_9
  nlinarith [h_sqrt5_bound, Real.sqrt_nonneg 5, sqrt5_sq]

/-! ### Main bound lemma for word1/word2

The upper bound for c in word1: c < 2*length1 - 1 = (1-sqrt5)/2 ~ -0.618.
Since the parabola f(c) = ||A + cB||^2 is upward-opening (coefficient of c^2 is ||B||^2 > 0),
and [-1, c_upper] is entirely to the left of the vertex, the maximum is at c = -1.

For c in [-1, c_upper], we have ||expression|| <= value_at_neg1 <= r_crit.
-/



/-! ### Helper lemmas for upper endpoint calculation -/

/-- sin^2(pi/5) = (5-sqrt5)/8 -/
lemma sin_sq_pi_div_5 : Real.sin (π / 5)^2 = (5 - √5) / 8 := by
  have h_cos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have h := Real.sin_sq_add_cos_sq (π / 5)
  have h1 : Real.sin (π / 5)^2 = 1 - Real.cos (π / 5)^2 := by linarith
  grind

/-- (sqrt5-1)^2 = 6 - 2*sqrt5 -/
lemma sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by grind

/-- Im(zeta5^2) = sin(pi/5) -/
lemma zeta5_sq_im' : (ζ₅^2).im = Real.sin (π / 5) := by
  rw [zeta5_sq_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
             Complex.I_im, Complex.I_re, Complex.ofReal_re]
  have h : Real.sin (4 * π / 5) = Real.sin (π / 5) := by
    rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.sin_pi_sub]
  linarith [h]

/-- Im(zeta5^3) = -sin(pi/5) -/
lemma zeta5_cubed_im' : (ζ₅^3).im = -Real.sin (π / 5) := by
  rw [zeta5_cubed_eq, Complex.exp_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
             Complex.cos_ofReal_im, Complex.sin_ofReal_re, mul_zero, mul_one, zero_add]
  rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring, Real.sin_add_pi]
  ring

/-- Im(zeta5^4) = -sin(2pi/5) -/
lemma zeta5_pow4_im' : (ζ₅^4).im = -Real.sin (2 * π / 5) := by
  have : ζ₅^4 = starRingEnd ℂ ζ₅ := by rw [← zeta5_conj]
  rw [this, Complex.conj_im, zeta5_im_eq_sin]

/-- Re(B) = -sqrt5/2 where B = zeta5^3 - zeta5^4 -/
lemma B_re' : (ζ₅^3 - ζ₅^4).re = -√5 / 2 := by
  simp only [Complex.sub_re]
  rw [zeta5_cubed_re, zeta5_pow4_re]
  ring

/-- Im(B) where B = zeta5^3 - zeta5^4 -/
lemma B_im : (ζ₅^3 - ζ₅^4).im = Real.sin (2 * π / 5) - Real.sin (π / 5) := by
  simp only [Complex.sub_im]
  rw [zeta5_cubed_im', zeta5_pow4_im']
  ring

/-- ||B||^2 = (5-sqrt5)/2 where B = zeta5^3 - zeta5^4 -/
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
  rw [h2, h3, h_sin_sq, sqrt5_minus_1_sq]
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

/-- Re(A*conj(B)) = 3*sqrt5/2 where A = -2 + zeta5^2, B = zeta5^3 - zeta5^4 -/
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

/-- The vertex of f(c) = ||A + cB||^2 is at c_v < -1 -/
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

/-- normSq at upper endpoint equals 3 + phi -/
lemma normSq_at_upper_endpoint :
    Complex.normSq ((-2 : ℂ) + ζ₅^2 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4)) = 3 + φ := by
  have h_sin_sq := sin_sq_pi_div_5
  have h_sq := sqrt5_minus_1_sq

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
