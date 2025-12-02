/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Core
import TDCSG.MainTheorem
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Isometry

/-!
# Properties of the Fifth Root of Unity

This file establishes algebraic and trigonometric properties of ζ₅, the primitive fifth root of
unity, including its relationship to the golden ratio and cosine values at multiples of π/5.

## Main results

- `zeta5_isPrimitiveRoot`: ζ₅ is a primitive fifth root of unity
- `zeta5_eq`: ζ₅ equals cos(2π/5) + i·sin(2π/5)
- `cos_two_pi_fifth`: cos(2π/5) equals (φ - 1)/2 where φ is the golden ratio
- `cyclotomic5_sum`: The sum 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ equals zero

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (ζ₅ zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit zeta5_isPrimitiveRoot zeta5_abs)

@[simp] lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

lemma three_plus_phi_pos : 0 < 3 + φ := by
  unfold φ
  have := Real.goldenRatio_pos
  linarith

lemma one_plus_phi_pos : 0 < 1 + φ := by
  unfold φ
  linarith [Real.goldenRatio_pos]

@[simp] lemma zeta5_pow_five : ζ₅ ^ 5 = 1 :=
  (zeta5_isPrimitiveRoot).pow_eq_one

@[simp] lemma zeta5_pow_zero : ζ₅ ^ 0 = 1 := pow_zero ζ₅

@[simp] lemma zeta5_pow_zero_re : (ζ₅ ^ 0).re = 1 := by simp

@[simp] lemma zeta5_pow_zero_im : (ζ₅ ^ 0).im = 0 := by simp

lemma zeta5_ne_one : ζ₅ ≠ 1 := by
  unfold ζ₅
  have : (2 : ℝ) * π / 5 ≠ 0 := by
    apply div_ne_zero
    apply mul_ne_zero
    · norm_num
    · exact Real.pi_ne_zero
    · norm_num
  intro h
  rw [show (exp (2 * ↑π * I / 5) : ℂ) =
      exp ((2 * π / 5 : ℝ) * I) by
    congr 1
    push_cast
    ring] at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have : (2 * π / 5 : ℝ) = k * (2 * π) := by
    have h_eq : ((2 * π / 5 : ℝ) * I : ℂ) =
        (k : ℂ) * ((2 * π : ℝ) * I) := by
      convert hk using 2
      push_cast
      ring
    have h_im := congr_arg Complex.im h_eq
    simp at h_im
    exact h_im
  have : (1 : ℝ) / 5 = k := by
    field_simp at this
    linarith [Real.pi_pos]
  have h_real : (k : ℝ) * 5 = 1 := by linarith
  have h_int : k * 5 = 1 := by
    have : (k : ℝ) * (5 : ℝ) = (1 : ℝ) := h_real
    norm_cast at this
  have : (1 : ℤ) % 5 = 0 := by rw [← h_int]; simp
  norm_num at this

@[simp] lemma zeta5_abs_pow (n : ℕ) : ‖ζ₅^n‖ = 1 := by
  rw [Complex.norm_pow, zeta5_abs, one_pow]

lemma zeta5_abs_pow4 : ‖ζ₅^4‖ = 1 := zeta5_abs_pow 4

lemma zeta5_pow_ne_one {k : ℕ} (hk : k ≠ 0) (hk5 : k < 5) : ζ₅ ^ k ≠ 1 :=
  zeta5_isPrimitiveRoot.pow_ne_one_of_pos_of_lt hk hk5

lemma cos_two_pi_fifth :
    Real.cos (2 * π / 5) = (Real.goldenRatio - 1) / 2 := by
  rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring]
  rw [Real.cos_two_mul]
  rw [Real.cos_pi_div_five]
  unfold Real.goldenRatio
  rw [show (2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1 : ℝ) =
      (Real.sqrt 5 - 1) / 4 by
    have h : (1 + Real.sqrt 5) ^ 2 =
        6 + 2 * Real.sqrt 5 := by
      rw [add_sq]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    calc 2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1
        = 2 * (1 + Real.sqrt 5) ^ 2 / 16 - 1 := by ring
      _ = 2 * (6 + 2 * Real.sqrt 5) / 16 - 1 := by
          rw [h]
      _ = (12 + 4 * Real.sqrt 5) / 16 - 1 := by ring
      _ = (12 + 4 * Real.sqrt 5 - 16) / 16 := by ring
      _ = (4 * Real.sqrt 5 - 4) / 16 := by ring
      _ = (Real.sqrt 5 - 1) / 4 := by ring]
  rw [show ((1 + Real.sqrt 5) / 2 - 1) / 2 =
      (Real.sqrt 5 - 1) / 4 by
    field_simp; ring]

@[simp] lemma zeta5_conj : starRingEnd ℂ ζ₅ = ζ₅^4 := by
  have h5 : ζ₅ ^ 5 = 1 := zeta5_pow_five
  unfold ζ₅
  rw [← Complex.exp_conj]
  rw [map_div₀, map_mul, map_mul]
  simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [show (2 * ↑π * -I / 5 : ℂ) = -(2 * ↑π * I / 5) by ring]
  rw [Complex.exp_neg, ← Complex.exp_nat_mul]
  norm_num
  field_simp [Complex.exp_ne_zero]
  unfold ζ₅ at h5
  rw [← Complex.exp_nat_mul] at h5
  ring_nf at h5 ⊢
  rw [← Complex.exp_add]
  convert h5.symm using 2
  ring

@[simp] lemma zeta5_inv_eq_pow4 : ζ₅⁻¹ = ζ₅^4 := by
  have h1 : ζ₅^5 = 1 := zeta5_pow_five
  have h2 : ζ₅ ≠ 0 := by
    intro h
    rw [h] at h1
    norm_num at h1
  field_simp [h2]
  rw [← h1]

lemma zeta5_ne_zero : ζ₅ ≠ 0 := by
  intro h
  have h1 : ζ₅^5 = 1 := zeta5_pow_five
  rw [h] at h1
  norm_num at h1

lemma zeta5_pow_reduce (n : ℕ) : ζ₅ ^ n = ζ₅ ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul]
  simp [zeta5_pow_five]

@[simp] lemma zeta5_pow_add_five_mul (n k : ℕ) : ζ₅ ^ (n + 5 * k) = ζ₅ ^ n := by
  rw [pow_add, pow_mul, zeta5_pow_five, one_pow, mul_one]

lemma zeta5_inv_mul : ζ₅⁻¹ * ζ₅ = 1 := by
  field_simp [zeta5_ne_zero]

lemma cyclotomic5_sum : 1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0 := by
  have h1 : ζ₅^5 = 1 := zeta5_pow_five
  have h2 : ζ₅ ≠ 1 := zeta5_ne_one
  have h3 : ζ₅ - 1 ≠ 0 := sub_ne_zero_of_ne h2

  have h_factor : ζ₅^5 - 1 = (ζ₅ - 1) * (ζ₅^4 + ζ₅^3 + ζ₅^2 + ζ₅ + 1) := by ring
  rw [h1] at h_factor
  have h_zero : (ζ₅ - 1) * (ζ₅^4 + ζ₅^3 + ζ₅^2 + ζ₅ + 1) = 0 := by
    calc (ζ₅ - 1) * (ζ₅^4 + ζ₅^3 + ζ₅^2 + ζ₅ + 1)
        = ζ₅^5 - 1 := by ring
      _ = 1 - 1 := by rw [h1]
      _ = 0 := by ring
  have : ζ₅^4 + ζ₅^3 + ζ₅^2 + ζ₅ + 1 = 0 := by
    have := mul_eq_zero.mp h_zero
    cases this with
    | inl h => exact absurd h h3
    | inr h => exact h
  calc 1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4
      = ζ₅^4 + ζ₅^3 + ζ₅^2 + ζ₅ + 1 := by ring
    _ = 0 := this

@[simp] lemma zeta5_pow_six : ζ₅^6 = ζ₅ := by
  have : ζ₅^6 = ζ₅^(6 % 5) := zeta5_pow_reduce 6
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_seven : ζ₅^7 = ζ₅^2 := by
  have : ζ₅^7 = ζ₅^(7 % 5) := zeta5_pow_reduce 7
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_eight : ζ₅^8 = ζ₅^3 := by
  have : ζ₅^8 = ζ₅^(8 % 5) := zeta5_pow_reduce 8
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_nine : ζ₅^9 = ζ₅^4 := by
  have : ζ₅^9 = ζ₅^(9 % 5) := zeta5_pow_reduce 9
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_ten : ζ₅^10 = 1 := by
  have : ζ₅^10 = ζ₅^(10 % 5) := zeta5_pow_reduce 10
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_eleven : ζ₅^11 = ζ₅ := by
  have : ζ₅^11 = ζ₅^(11 % 5) := zeta5_pow_reduce 11
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_twelve : ζ₅^12 = ζ₅^2 := by
  have : ζ₅^12 = ζ₅^(12 % 5) := zeta5_pow_reduce 12
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_thirteen : ζ₅^13 = ζ₅^3 := by
  have : ζ₅^13 = ζ₅^(13 % 5) := zeta5_pow_reduce 13
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_fifteen : ζ₅^15 = 1 := by
  have : ζ₅^15 = ζ₅^(15 % 5) := zeta5_pow_reduce 15
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_sixteen : ζ₅^16 = ζ₅ := by
  have : ζ₅^16 = ζ₅^(16 % 5) := zeta5_pow_reduce 16
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_seventeen : ζ₅^17 = ζ₅^2 := by
  have : ζ₅^17 = ζ₅^(17 % 5) := zeta5_pow_reduce 17
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_fourteen : ζ₅^14 = ζ₅^4 := by
  have : ζ₅^14 = ζ₅^(14 % 5) := zeta5_pow_reduce 14
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_eighteen : ζ₅^18 = ζ₅^3 := by
  have : ζ₅^18 = ζ₅^(18 % 5) := zeta5_pow_reduce 18
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_nineteen : ζ₅^19 = ζ₅^4 := by
  have : ζ₅^19 = ζ₅^(19 % 5) := zeta5_pow_reduce 19
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_twenty : ζ₅^20 = 1 := by
  have : ζ₅^20 = ζ₅^(20 % 5) := zeta5_pow_reduce 20
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_twentythree : ζ₅^23 = ζ₅^3 := by
  have : ζ₅^23 = ζ₅^(23 % 5) := zeta5_pow_reduce 23
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_twentyfour : ζ₅^24 = ζ₅^4 := by
  have : ζ₅^24 = ζ₅^(24 % 5) := zeta5_pow_reduce 24
  norm_num at this
  exact this

@[simp] lemma zeta5_pow_five_C : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
@[simp] lemma zeta5_pow_ten_C : ζ₅^10 = (1 : ℂ) := zeta5_pow_ten
@[simp] lemma zeta5_pow_fifteen_C : ζ₅^15 = (1 : ℂ) := zeta5_pow_fifteen
@[simp] lemma zeta5_pow_twenty_C : ζ₅^20 = (1 : ℂ) := zeta5_pow_twenty

lemma zeta5_re_eq_cos : ζ₅.re = Real.cos (2 * π / 5) := by
  unfold ζ₅
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]; ring]
  exact Complex.exp_ofReal_mul_I_re (2 * π / 5)

@[simp] lemma zeta5_im_eq_sin : ζ₅.im = Real.sin (2 * π / 5) := by
  unfold ζ₅
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]; ring]
  exact Complex.exp_ofReal_mul_I_im (2 * π / 5)

lemma zeta5_sq_eq : ζ₅^2 = ↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5)) := by
  unfold ζ₅
  rw [sq, show (exp (2 * ↑π * I / 5) : ℂ) * exp (2 * ↑π * I / 5) =
      exp ((2 * π / 5 : ℝ) * I + (2 * π / 5 : ℝ) * I) by
    rw [← Complex.exp_add]; congr 1; push_cast; field_simp]
  rw [show (2 * π / 5 : ℝ) * I + (2 * π / 5 : ℝ) * I = (4 * π / 5 : ℝ) * I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

@[simp] lemma zeta5_re : ζ₅.re = (Real.sqrt 5 - 1) / 4 := by
  rw [zeta5_re_eq_cos, cos_two_pi_fifth]
  unfold Real.goldenRatio
  ring

lemma zeta5_re_eq_phi : ζ₅.re = (Real.goldenRatio - 1) / 2 := by
  rw [zeta5_re_eq_cos, cos_two_pi_fifth]

lemma cos_four_pi_fifth : Real.cos (4 * π / 5) = -Real.cos (π / 5) := by
  rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.cos_pi_sub]

lemma cos_four_pi_fifth_val : Real.cos (4 * π / 5) = -(Real.sqrt 5 + 1) / 4 := by
  rw [cos_four_pi_fifth, Real.cos_pi_div_five]
  ring

@[simp] lemma zeta5_sq_re : (ζ₅^2).re = -(Real.sqrt 5 + 1) / 4 := by
  rw [zeta5_sq_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
             Complex.I_re, Complex.I_im, Complex.ofReal_im]
  rw [cos_four_pi_fifth_val]
  ring

lemma zeta5_cubed_eq : ζ₅^3 = Complex.exp ((6 * π / 5 : ℝ) * I) := by
  unfold ζ₅
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma cos_six_pi_fifth : Real.cos (6 * π / 5) = -(Real.sqrt 5 + 1) / 4 := by
  rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring]
  rw [Real.cos_add_pi, Real.cos_pi_div_five]
  ring

@[simp] lemma zeta5_cubed_re : (ζ₅^3).re = -(Real.sqrt 5 + 1) / 4 := by
  rw [zeta5_cubed_eq]
  rw [Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp only [mul_zero, mul_one]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  simp only [sub_zero, add_zero]
  exact cos_six_pi_fifth

@[simp] lemma zeta5_pow4_re : (ζ₅^4).re = (Real.sqrt 5 - 1) / 4 := by
  have h : (ζ₅^4).re = (starRingEnd ℂ ζ₅).re := by
    rw [← zeta5_conj]
  rw [h, Complex.conj_re, zeta5_re]

lemma zeta5_pow4_im_neg : (ζ₅^4).im = -ζ₅.im := by
  have h : ζ₅^4 = starRingEnd ℂ ζ₅ := by rw [← zeta5_conj]
  rw [h, Complex.conj_im]

lemma sin_four_pi_fifth : Real.sin (4 * π / 5) = Real.sin (π / 5) := by
  rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.sin_pi_sub]

lemma sin_six_pi_fifth : Real.sin (6 * π / 5) = -Real.sin (π / 5) := by
  rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring, Real.sin_add_pi]

lemma zeta5_sq_im : (ζ₅^2).im = Real.sin (4 * π / 5) := by
  rw [zeta5_sq_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
             Complex.I_re, Complex.I_im, Complex.ofReal_re]
  ring

lemma zeta5_cubed_eq_trig : ζ₅^3 = ↑(Real.cos (6 * π / 5)) + I * ↑(Real.sin (6 * π / 5)) := by
  rw [zeta5_cubed_eq]
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

lemma zeta5_cubed_im : (ζ₅^3).im = Real.sin (6 * π / 5) := by
  rw [zeta5_cubed_eq_trig]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
             Complex.I_re, Complex.I_im, Complex.ofReal_re]
  ring

@[simp] lemma zeta5_pow4_im : (ζ₅^4).im = -Real.sin (2 * π / 5) := by
  rw [zeta5_pow4_im_neg, zeta5_im_eq_sin]

@[simp] lemma zeta5_sq_im_eq : (ζ₅^2).im = Real.sin (π / 5) := by
  rw [zeta5_sq_im, sin_four_pi_fifth]

@[simp] lemma zeta5_cubed_im_eq : (ζ₅^3).im = -Real.sin (π / 5) := by
  rw [zeta5_cubed_im, sin_six_pi_fifth]

lemma zeta5_cubed_im_neg : (ζ₅^3).im < 0 := by
  rw [zeta5_cubed_im_eq]
  apply neg_neg_of_pos
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

/-- sin²(π/5) = (5 - √5)/8 -/
@[simp] lemma sin_sq_pi_div_5 : Real.sin (π / 5)^2 = (5 - √5) / 8 := by
  have h_cos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have h := Real.sin_sq_add_cos_sq (π / 5)
  have h1 : Real.sin (π / 5)^2 = 1 - Real.cos (π / 5)^2 := by linarith
  grind

/-- sin²(2π/5) = (5 + √5)/8 -/
@[simp] lemma sin_sq_two_pi_div_5 : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := by
  have h_sin_double : Real.sin (2 * π / 5) = 2 * Real.sin (π / 5) * Real.cos (π / 5) := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
  have h_cos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  rw [h_sin_double, h_cos]
  calc (2 * Real.sin (π / 5) * ((1 + √5) / 4))^2
      = 4 * Real.sin (π / 5)^2 * ((1 + √5) / 4)^2 := by ring
    _ = 4 * ((5 - √5) / 8) * ((1 + √5)^2 / 16) := by rw [h_sin_sq]; ring
    _ = (5 + √5) / 8 := by nlinarith [sqrt5_sq]

/-- ‖1 - ζ₅‖² = (5 - √5)/2 -/
@[simp] lemma normSq_one_sub_zeta5 : Complex.normSq (1 - ζ₅) = (5 - √5) / 2 := by
  rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_apply, zeta5_re, zeta5_im_eq_sin]
  have h1 : (√5 - 1) / 4 * ((√5 - 1) / 4) + Real.sin (2 * π / 5) * Real.sin (2 * π / 5) = 1 := by
    have : Real.sin (2 * π / 5) * Real.sin (2 * π / 5) = (5 + √5) / 8 := by
      rw [← sq, sin_sq_two_pi_div_5]
    rw [this]
    nlinarith [sqrt5_sq]
  have h_re : ((1 : ℂ) * starRingEnd ℂ ζ₅).re = ζ₅.re := by simp
  rw [h1, h_re, zeta5_re]
  ring

/-- conj(1 - ζ₅) = 1 - ζ₅⁴ -/
@[simp] lemma conj_one_sub_zeta5 : starRingEnd ℂ (1 - ζ₅) = 1 - ζ₅^4 := by
  rw [map_sub, map_one, zeta5_conj]

/-- ‖ζ₅³ - ζ₅⁴‖² = (5 - √5)/2 -/
@[simp] lemma normSq_zeta5_cubed_sub_pow4 : Complex.normSq (ζ₅^3 - ζ₅^4) = (5 - √5) / 2 := by
  rw [Complex.normSq_sub, Complex.normSq_apply, Complex.normSq_apply]
  simp only [zeta5_cubed_re, zeta5_cubed_im_eq, zeta5_pow4_re, zeta5_pow4_im]
  have h_conj_pow4 : starRingEnd ℂ (ζ₅^4) = ζ₅ := by
    rw [map_pow, zeta5_conj]
    calc (ζ₅^4)^4 = ζ₅^16 := by ring
      _ = ζ₅ := zeta5_pow_sixteen
  have h_re : ((ζ₅^3) * starRingEnd ℂ (ζ₅^4)).re = ((ζ₅^3) * ζ₅).re := by
    rw [h_conj_pow4]
  have h_prod : (ζ₅^3) * ζ₅ = ζ₅^4 := by ring
  rw [h_re, h_prod]
  simp only [zeta5_pow4_re]
  have h_sin_pi5 : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_sin_2pi5 : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  nlinarith [sqrt5_sq]

/-- (√5 - 1)² = 6 - 2√5 -/
lemma sqrt5_minus_one_sq : (√5 - 1)^2 = 6 - 2*√5 := by grind

end TDCSG.CompoundSymmetry.GG5
