/-
Copyright (c) 2025-10-18 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Isometry

/-!
# Fifth Roots of Unity

This file provides all algebraic identities for ζ₅ needed for the GG5 proof.

The core definition `zeta5` and `ζ₅` are in TDCSG.Definitions.Core.
Here we provide all the lemmas about the 5th root of unity.

The critical radius r_crit is imported from TDCSG.Definitions.Core.

## Main Definitions

* `ζ₅`: Unicode alias for `zeta5`, the primitive 5th root of unity e^(2πi/5)
* `zeta5Circle`: ζ₅ as an element of Mathlib's `Circle` type (unit complex numbers)

## Main Results

* `zeta5_pow_five`: ζ₅^5 = 1
* `zeta5_isPrimitiveRoot`: ζ₅ is a primitive 5th root of unity
* `cyclotomic5_sum`: 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0
* `zeta5_abs`: |ζ₅| = 1
* `circle_exp_two_pi_fifth`: Circle.exp (2π/5) = zeta5Circle
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real TDCSG.Definitions

-- ζ₅ is imported from TDCSG.Definitions.Core via the open statement below

/-! ### Critical Radius Lemmas -/

/-- The critical radius satisfies 2.148 < r_crit < 2.150. -/
lemma r_crit_approx : 2.148 < r_crit ∧ r_crit < 2.150 := by
  unfold r_crit φ
  constructor
  · rw [show (2.148 : ℝ) = Real.sqrt (2.148 ^ 2) by
      rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt
    · norm_num
    have h_sq : (2.148 : ℝ) ^ 2 = 4.613904 := by norm_num
    rw [h_sq]
    have φ_lower : (1.613904 : ℝ) < Real.goldenRatio := by
      have h1 : (2.227808 : ℝ) ^ 2 < 5 := by norm_num
      have h2 : (2.227808 : ℝ) < Real.sqrt 5 := by
        rw [show (2.227808 : ℝ) =
            Real.sqrt (2.227808 ^ 2) by
          rw [Real.sqrt_sq]; norm_num]
        exact Real.sqrt_lt_sqrt (by norm_num) h1
      unfold Real.goldenRatio
      linarith
    linarith
  · rw [show (2.150 : ℝ) = Real.sqrt (2.150 ^ 2) by
      rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt
    · linarith [Real.goldenRatio_pos]
    have h_sq : (2.150 : ℝ) ^ 2 = 4.6225 := by norm_num
    rw [h_sq]
    have φ_upper : Real.goldenRatio < (1.6225 : ℝ) := by
      unfold Real.goldenRatio
      have h1 : 5 < (2.245 : ℝ) ^ 2 := by norm_num
      have h2 : Real.sqrt 5 < (2.245 : ℝ) := by
        rw [show (2.245 : ℝ) =
            Real.sqrt (2.245 ^ 2) by
          rw [Real.sqrt_sq]; norm_num]
        exact Real.sqrt_lt_sqrt (by norm_num) h1
      linarith
    linarith


/-! ### 5th Roots of Unity -/

/-- ζ₅ is a 5th root of unity. -/
lemma zeta5_pow_five : ζ₅ ^ 5 = 1 := by
  unfold ζ₅ zeta5
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  ring

/-- ζ₅ is not equal to 1. -/
lemma zeta5_ne_one : ζ₅ ≠ 1 := by
  unfold ζ₅ zeta5
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

/-- |ζ₅| = 1 -/
lemma zeta5_abs : ‖ζ₅‖ = 1 := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]
    ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * π / 5)

/-! ### Primitive Root Infrastructure -/

/-- ζ₅ is a primitive 5th root of unity. -/
lemma zeta5_isPrimitiveRoot : IsPrimitiveRoot ζ₅ 5 := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = 2 * π * I / (5 : ℂ) by norm_cast]
  exact Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- Powers of ζ₅ less than 5 are not equal to 1. -/
lemma zeta5_pow_ne_one {k : ℕ} (hk : k ≠ 0) (hk5 : k < 5) : ζ₅ ^ k ≠ 1 :=
  zeta5_isPrimitiveRoot.pow_ne_one_of_pos_of_lt hk hk5

/-- ζ₅^k = 1 if and only if 5 divides k. -/
lemma zeta5_pow_eq_one_iff {k : ℕ} : ζ₅ ^ k = 1 ↔ 5 ∣ k := by
  exact zeta5_isPrimitiveRoot.pow_eq_one_iff_dvd k

/-! ### Trigonometric Identities -/

/-- The identity cos(2π/5) = (φ - 1)/2. -/
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

/-- The conjugate of ζ₅ equals ζ₅⁴. -/
lemma zeta5_conj : starRingEnd ℂ ζ₅ = ζ₅^4 := by
  have h5 : ζ₅ ^ 5 = 1 := zeta5_pow_five
  unfold ζ₅ zeta5
  rw [← Complex.exp_conj]
  rw [map_div₀, map_mul, map_mul]
  simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [show (2 * ↑π * -I / 5 : ℂ) = -(2 * ↑π * I / 5) by ring]
  rw [Complex.exp_neg, ← Complex.exp_nat_mul]
  norm_num
  field_simp [Complex.exp_ne_zero]
  unfold ζ₅ zeta5 at h5
  rw [← Complex.exp_nat_mul] at h5
  ring_nf at h5 ⊢
  rw [← Complex.exp_add]
  convert h5.symm using 2
  ring

/-- The inverse of ζ₅ equals ζ₅⁴. -/
lemma zeta5_inv_eq_pow4 : ζ₅⁻¹ = ζ₅^4 := by
  have h1 : ζ₅^5 = 1 := zeta5_pow_five
  have h2 : ζ₅ ≠ 0 := by
    intro h
    rw [h] at h1
    norm_num at h1
  field_simp [h2]
  rw [← h1]

/-! ### Fifth root of unity computation helpers

These lemmas help simplify expressions involving compositions of rotations.
The key insight is that ζ₅⁵ = 1, so all powers reduce to ζ₅^(n mod 5).

Usage pattern for endpoint calculations:
1. Use `zeta5_inv_as_pow4` to convert ζ₅⁻¹ → ζ₅⁴
2. Use `pow_add` to combine powers: ζ₅ⁿ * ζ₅ᵐ = ζ₅ⁿ⁺ᵐ
3. Use `zeta5_pow_reduce` to normalize: ζ₅ⁿ = ζ₅^(n mod 5)
4. Specific helpers like `zeta5_sq_mul_inv` shortcut common patterns

Example: Simplify (z + 1) * ζ₅² * ζ₅⁻¹
  Step 1: Rewrite ζ₅⁻¹ as ζ₅⁴ using `zeta5_inv_as_pow4`
          → (z + 1) * ζ₅² * ζ₅⁴
  Step 2: Combine powers using `pow_add`
          → (z + 1) * ζ₅⁶
  Step 3: Reduce using `zeta5_pow_reduce`
          → (z + 1) * ζ₅  (since 6 mod 5 = 1)
  Or use the direct helper `zeta5_sq_mul_inv` in one step.
-/

/-- ζ₅ is not zero. -/
lemma zeta5_ne_zero : ζ₅ ≠ 0 := by
  intro h
  have h1 : ζ₅^5 = 1 := zeta5_pow_five
  rw [h] at h1
  norm_num at h1

/-- Reduce powers of ζ₅ using ζ₅⁵ = 1 -/
lemma zeta5_pow_reduce (n : ℕ) : ζ₅ ^ n = ζ₅ ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul]
  simp [zeta5_pow_five]

/-- Simplify ζ₅⁻¹ * ζ₅ -/
lemma zeta5_inv_mul : ζ₅⁻¹ * ζ₅ = 1 := by
  field_simp [zeta5_ne_zero]

/-- Simplify ζ₅ * ζ₅⁻¹ -/
lemma zeta5_mul_inv : ζ₅ * ζ₅⁻¹ = 1 := by
  field_simp [zeta5_ne_zero]

/-- Express ζ₅⁻¹ as ζ₅⁴ for easier computation -/
lemma zeta5_inv_as_pow4 : ζ₅⁻¹ = ζ₅^4 := zeta5_inv_eq_pow4

/-- Product of positive and negative powers: ζ₅ⁿ * ζ₅⁻¹ = ζ₅ⁿ⁻¹ -/
lemma zeta5_pow_mul_inv (n : ℕ) : ζ₅^n * ζ₅⁻¹ = ζ₅^((n + 4) % 5) := by
  rw [zeta5_inv_as_pow4]
  rw [← pow_add]
  exact zeta5_pow_reduce (n + 4)

/-- Product of negative and positive powers: ζ₅⁻¹ * ζ₅ⁿ = ζ₅ⁿ⁻¹ -/
lemma zeta5_inv_mul_pow (n : ℕ) : ζ₅⁻¹ * ζ₅^n = ζ₅^((n + 4) % 5) := by
  rw [mul_comm]
  exact zeta5_pow_mul_inv n

/-- Useful for ζ₅² * ζ₅⁻¹ = ζ₅ -/
lemma zeta5_sq_mul_inv : ζ₅^2 * ζ₅⁻¹ = ζ₅ := by
  have : ζ₅^2 * ζ₅⁻¹ = ζ₅^((2 + 4) % 5) := zeta5_pow_mul_inv 2
  norm_num at this
  exact this

/-- Useful for ζ₅⁴ * ζ₅² = ζ₅ -/
lemma zeta5_pow4_mul_sq : ζ₅^4 * ζ₅^2 = ζ₅ := by
  rw [← pow_add]
  have : ζ₅^6 = ζ₅^(6 % 5) := zeta5_pow_reduce 6
  norm_num at this
  exact this

/-- The 5th cyclotomic polynomial relation: 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0.
    Since ζ₅^5 = 1 and ζ₅ ≠ 1, we have (ζ₅ - 1)(ζ₅⁴ + ζ₅³ + ζ₅² + ζ₅ + 1) = 0 -/
lemma cyclotomic5_sum : 1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0 := by
  have h1 : ζ₅^5 = 1 := zeta5_pow_five
  have h2 : ζ₅ ≠ 1 := zeta5_ne_one
  have h3 : ζ₅ - 1 ≠ 0 := sub_ne_zero_of_ne h2
  -- Use the factorization: ζ₅^5 - 1 = (ζ₅ - 1)(ζ₅⁴ + ζ₅³ + ζ₅² + ζ₅ + 1)
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

/-- Express ζ₅⁴ in terms of lower powers using the cyclotomic polynomial -/
lemma zeta5_pow4_eq : ζ₅^4 = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by
  have h := cyclotomic5_sum
  -- From 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0, we get ζ₅⁴ = -(1 + ζ₅ + ζ₅² + ζ₅³)
  have h2 : ζ₅^4 + (1 + ζ₅ + ζ₅^2 + ζ₅^3) = 0 := by
    calc ζ₅^4 + (1 + ζ₅ + ζ₅^2 + ζ₅^3)
        = 1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 := by ring
      _ = 0 := h
  calc ζ₅^4 = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + (ζ₅^4 + (1 + ζ₅ + ζ₅^2 + ζ₅^3)) := by ring
    _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + 0 := by rw [h2]
    _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) := by ring
    _ = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by ring

/-- Helper lemmas for reducing higher powers of ζ₅ -/
lemma zeta5_pow_six : ζ₅^6 = ζ₅ := by
  have : ζ₅^6 = ζ₅^(6 % 5) := zeta5_pow_reduce 6
  norm_num at this
  exact this

lemma zeta5_pow_seven : ζ₅^7 = ζ₅^2 := by
  have : ζ₅^7 = ζ₅^(7 % 5) := zeta5_pow_reduce 7
  norm_num at this
  exact this

lemma zeta5_pow_eight : ζ₅^8 = ζ₅^3 := by
  have : ζ₅^8 = ζ₅^(8 % 5) := zeta5_pow_reduce 8
  norm_num at this
  exact this

lemma zeta5_pow_nine : ζ₅^9 = ζ₅^4 := by
  have : ζ₅^9 = ζ₅^(9 % 5) := zeta5_pow_reduce 9
  norm_num at this
  exact this

lemma zeta5_pow_ten : ζ₅^10 = 1 := by
  have : ζ₅^10 = ζ₅^(10 % 5) := zeta5_pow_reduce 10
  norm_num at this
  exact this

lemma zeta5_pow_eleven : ζ₅^11 = ζ₅ := by
  have : ζ₅^11 = ζ₅^(11 % 5) := zeta5_pow_reduce 11
  norm_num at this
  exact this

lemma zeta5_pow_twelve : ζ₅^12 = ζ₅^2 := by
  have : ζ₅^12 = ζ₅^(12 % 5) := zeta5_pow_reduce 12
  norm_num at this
  exact this

lemma zeta5_pow_thirteen : ζ₅^13 = ζ₅^3 := by
  have : ζ₅^13 = ζ₅^(13 % 5) := zeta5_pow_reduce 13
  norm_num at this
  exact this

lemma zeta5_pow_fifteen : ζ₅^15 = 1 := by
  have : ζ₅^15 = ζ₅^(15 % 5) := zeta5_pow_reduce 15
  norm_num at this
  exact this

lemma zeta5_pow_sixteen : ζ₅^16 = ζ₅ := by
  have : ζ₅^16 = ζ₅^(16 % 5) := zeta5_pow_reduce 16
  norm_num at this
  exact this

lemma zeta5_pow_seventeen : ζ₅^17 = ζ₅^2 := by
  have : ζ₅^17 = ζ₅^(17 % 5) := zeta5_pow_reduce 17
  norm_num at this
  exact this

/-- ζ₅.re = cos(2π/5). -/
lemma zeta5_re_eq_cos : ζ₅.re = Real.cos (2 * π / 5) := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]; ring]
  exact Complex.exp_ofReal_mul_I_re (2 * π / 5)

/-- ζ₅.im = sin(2π/5). -/
lemma zeta5_im_eq_sin : ζ₅.im = Real.sin (2 * π / 5) := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]; ring]
  exact Complex.exp_ofReal_mul_I_im (2 * π / 5)

/-- Helper: express ζ₅ in terms of cos and sin -/
lemma zeta5_eq : ζ₅ = ↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5)) := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by push_cast; field_simp]
  rw [Complex.exp_mul_I,  Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- Helper: express ζ₅² in terms of cos and sin -/
lemma zeta5_sq_eq : ζ₅^2 = ↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5)) := by
  unfold ζ₅ zeta5
  rw [sq, show (exp (2 * ↑π * I / 5) : ℂ) * exp (2 * ↑π * I / 5) =
      exp ((2 * π / 5 : ℝ) * I + (2 * π / 5 : ℝ) * I) by
    rw [← Complex.exp_add]; congr 1; push_cast; field_simp]
  rw [show (2 * π / 5 : ℝ) * I + (2 * π / 5 : ℝ) * I = (4 * π / 5 : ℝ) * I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-! ### Explicit ζ₅ values in terms of golden ratio

These give exact algebraic values for the real and imaginary parts of ζ₅ powers.
Key identities:
- cos(2π/5) = (√5 - 1)/4 = (φ - 1)/2
- cos(4π/5) = -(√5 + 1)/4 = -φ/2
-/

/-- ζ₅.re = (√5 - 1)/4 = (φ - 1)/2 -/
lemma zeta5_re : ζ₅.re = (Real.sqrt 5 - 1) / 4 := by
  rw [zeta5_re_eq_cos, cos_two_pi_fifth]
  unfold Real.goldenRatio
  ring

/-- ζ₅.re in terms of φ -/
lemma zeta5_re_eq_phi : ζ₅.re = (Real.goldenRatio - 1) / 2 := by
  rw [zeta5_re_eq_cos, cos_two_pi_fifth]

/-- ζ₅.im > 0 -/
lemma zeta5_im_pos : 0 < ζ₅.im := by
  rw [zeta5_im_eq_sin]
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

/-- cos(4π/5) = -cos(π/5) (supplementary angle identity) -/
lemma cos_four_pi_fifth : Real.cos (4 * π / 5) = -Real.cos (π / 5) := by
  rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.cos_pi_sub]

/-- cos(4π/5) = -(√5 + 1)/4 = -φ/2 (explicit value) -/
lemma cos_four_pi_fifth_val : Real.cos (4 * π / 5) = -(Real.sqrt 5 + 1) / 4 := by
  rw [cos_four_pi_fifth, Real.cos_pi_div_five]
  ring

/-- (ζ₅²).re = -(√5 + 1)/4 = -φ/2 -/
lemma zeta5_sq_re : (ζ₅^2).re = -(Real.sqrt 5 + 1) / 4 := by
  rw [zeta5_sq_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
             Complex.I_re, Complex.I_im, Complex.ofReal_im]
  rw [cos_four_pi_fifth_val]
  ring

/-- (ζ₅²).re in terms of φ -/
lemma zeta5_sq_re_eq_phi : (ζ₅^2).re = -Real.goldenRatio / 2 := by
  rw [zeta5_sq_re]
  unfold Real.goldenRatio
  ring

/-- ζ₅³ = exp(6πi/5) -/
lemma zeta5_cubed_eq : ζ₅^3 = Complex.exp ((6 * π / 5 : ℝ) * I) := by
  unfold ζ₅ zeta5
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- cos(6π/5) = cos(π + π/5) = -cos(π/5) -/
lemma cos_six_pi_fifth : Real.cos (6 * π / 5) = -(Real.sqrt 5 + 1) / 4 := by
  rw [show (6 * π / 5 : ℝ) = π / 5 + π by ring]
  rw [Real.cos_add_pi, Real.cos_pi_div_five]
  ring

/-- (ζ₅³).re = -(√5 + 1)/4 -/
lemma zeta5_cubed_re : (ζ₅^3).re = -(Real.sqrt 5 + 1) / 4 := by
  rw [zeta5_cubed_eq]
  rw [Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp only [mul_zero, mul_one]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  simp only [sub_zero, add_zero]
  exact cos_six_pi_fifth

/-- (ζ₅⁴).re = ζ₅.re (by conjugate symmetry: ζ₅⁴ = conj(ζ₅)) -/
lemma zeta5_pow4_re : (ζ₅^4).re = (Real.sqrt 5 - 1) / 4 := by
  have h : (ζ₅^4).re = (starRingEnd ℂ ζ₅).re := by
    rw [← zeta5_conj]
  rw [h, Complex.conj_re, zeta5_re]

/-- (ζ₅⁴).im = -ζ₅.im (by conjugate symmetry) -/
lemma zeta5_pow4_im_neg : (ζ₅^4).im = -ζ₅.im := by
  have h : ζ₅^4 = starRingEnd ℂ ζ₅ := by rw [← zeta5_conj]
  rw [h, Complex.conj_im]

/-! ### Useful algebraic identities for rotation compositions -/

/-- Key identity: 1 + ζ₅⁴ real part -/
lemma one_add_zeta5_pow4_re : (1 + ζ₅^4).re = 1 + (Real.sqrt 5 - 1) / 4 := by
  simp only [Complex.add_re, Complex.one_re, zeta5_pow4_re]

/-- 1 - ζ₅⁴ real part -/
lemma one_sub_zeta5_pow4_re : (1 - ζ₅^4).re = 1 - (Real.sqrt 5 - 1) / 4 := by
  simp only [Complex.sub_re, Complex.one_re, zeta5_pow4_re]

/-- Sum of all ζ₅ power real parts is -1 (from cyclotomic sum) -/
lemma zeta5_powers_re_sum : ζ₅.re + (ζ₅^2).re + (ζ₅^3).re + (ζ₅^4).re = -1 := by
  have h := cyclotomic5_sum
  have h_re := congr_arg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h_re
  linarith

/-! ### Circle Infrastructure

The `Circle` type from Mathlib represents unit complex numbers with group structure.
Using `Circle` instead of raw angles gives us certified linear isometries via `rotation`.
-/

/-- ζ₅ as an element of the unit circle in ℂ.
    This leverages Mathlib's `Circle` type which provides group structure on unit complex numbers. -/
noncomputable def zeta5Circle : Circle :=
  ⟨ζ₅, mem_sphere_zero_iff_norm.2 zeta5_abs⟩

/-- The coercion of zeta5Circle back to ℂ is ζ₅. -/
@[simp]
lemma zeta5Circle_coe : (zeta5Circle : ℂ) = ζ₅ := rfl

/-- Powers of ζ₅ as Circle elements. -/
noncomputable def zeta5CirclePow (n : ℕ) : Circle := zeta5Circle ^ n

/-- The coercion of zeta5Circle^n is ζ₅^n. -/
lemma zeta5CirclePow_coe (n : ℕ) : (zeta5CirclePow n : ℂ) = ζ₅ ^ n := by
  induction n with
  | zero => simp [zeta5CirclePow]
  | succ n ih =>
    simp only [zeta5CirclePow, pow_succ, Circle.coe_mul]
    rw [← zeta5CirclePow, ih, zeta5Circle_coe]

/-- ζ₅⁻¹ as a Circle element (equals ζ₅⁴ for clockwise rotation). -/
noncomputable def zeta5CircleInv : Circle := zeta5Circle⁻¹

/-- The coercion of zeta5CircleInv is ζ₅⁻¹. -/
@[simp]
lemma zeta5CircleInv_coe : (zeta5CircleInv : ℂ) = ζ₅⁻¹ := rfl

/-- ζ₅⁴ = ζ₅⁻¹ in Circle (since ζ₅⁵ = 1). -/
lemma zeta5CirclePow4_eq_inv : zeta5CirclePow 4 = zeta5CircleInv := by
  apply Circle.ext
  simp only [zeta5CirclePow, zeta5CircleInv, Circle.coe_inv, zeta5Circle_coe]
  show (zeta5Circle ^ 4 : ℂ) = ζ₅⁻¹
  simp only [pow_succ, pow_zero, zeta5Circle_coe, zeta5_inv_as_pow4]

/-- Circle.exp (2π/5) equals zeta5Circle.
    This connects Mathlib's Circle.exp to our ζ₅ definition. -/
lemma circle_exp_two_pi_fifth : Circle.exp (2 * π / 5) = zeta5Circle := by
  apply Circle.ext
  simp only [Circle.coe_exp, zeta5Circle_coe]
  unfold ζ₅ zeta5
  congr 1
  push_cast
  ring

end TDCSG.CompoundSymmetry.GG5
