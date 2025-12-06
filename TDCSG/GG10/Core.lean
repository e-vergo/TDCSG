/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Circle

/-!
# Core Definitions for GG(10,10)

This file contains the fundamental constants and properties specific to the two-disk
compound symmetry group GG(10,10) with 10-fold rotational symmetry.

## Main definitions

- `ζ₁₀`: The primitive 10th root of unity e^(2πi/10)
- `r_crit_10`: The critical radius √(4 - φ) at which GG(10,10) becomes infinite

## Key relationships

The 10th root of unity ζ₁₀ is related to the 5th root by ζ₁₀² = ζ₅. This means
cos(2π/10) = cos(π/5) and many GG10 identities can be derived from GG5 ones.

The critical segment for GG(10,10) is E'₁₀E₁₀ where E₁₀ = ζ₁₀ - ζ₁₀². Unlike GG5's
3-interval IET, GG10 induces a simpler 2-interval IET with rotation number 1/φ.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.GG10

open scoped Complex
open Complex Real
open TDCSG.Definitions (φ)

/-- The primitive 10th root of unity ζ₁₀ = e^(2πi/10) = e^(πi/5).

This root of unity is central to the analysis of GG(10,10). The 10th root satisfies
ζ₁₀¹⁰ = 1 and is related to the 5th root by ζ₁₀² = ζ₅.

For GG(10,10), the critical segment is defined by E₁₀ = ζ₁₀ - ζ₁₀², giving
E₁₀ = (0.5, -0.363271...) in Cartesian coordinates. -/
noncomputable def ζ₁₀ : ℂ := exp (2 * Real.pi * Complex.I / 10)

/-- ζ₁₀ is a primitive 10th root of unity. -/
lemma zeta10_isPrimitiveRoot : IsPrimitiveRoot ζ₁₀ 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

/-- The complex norm of ζ₁₀ equals 1. -/
@[simp] lemma zeta10_abs : ‖ζ₁₀‖ = 1 :=
  IsPrimitiveRoot.norm'_eq_one zeta10_isPrimitiveRoot (by norm_num)

/-- The 10th power of ζ₁₀ equals 1. -/
@[simp] lemma zeta10_pow_ten : ζ₁₀ ^ 10 = 1 :=
  zeta10_isPrimitiveRoot.pow_eq_one

/-- ζ₁₀ is nonzero. -/
lemma zeta10_ne_zero : ζ₁₀ ≠ 0 := by
  intro h
  have := zeta10_pow_ten
  rw [h] at this
  norm_num at this

/-- ζ₁₀ ≠ 1 since ζ₁₀ has exact order 10. -/
lemma zeta10_ne_one : ζ₁₀ ≠ 1 := by
  unfold ζ₁₀
  have : (2 : ℝ) * π / 10 ≠ 0 := by
    apply div_ne_zero
    apply mul_ne_zero
    · norm_num
    · exact Real.pi_ne_zero
    · norm_num
  intro h
  rw [show (exp (2 * ↑π * I / 10) : ℂ) =
      exp ((2 * π / 10 : ℝ) * I) by
    congr 1
    push_cast
    ring] at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have : (2 * π / 10 : ℝ) = k * (2 * π) := by
    have h_eq : ((2 * π / 10 : ℝ) * I : ℂ) =
        (k : ℂ) * ((2 * π : ℝ) * I) := by
      convert hk using 2
      push_cast
      ring
    have h_im := congr_arg Complex.im h_eq
    simp at h_im
    exact h_im
  have : (1 : ℝ) / 10 = k := by
    field_simp at this
    linarith [Real.pi_pos]
  have h_real : (k : ℝ) * 10 = 1 := by linarith
  have h_int : k * 10 = 1 := by
    have : (k : ℝ) * (10 : ℝ) = (1 : ℝ) := h_real
    norm_cast at this
  have : (1 : ℤ) % 10 = 0 := by rw [← h_int]; simp
  norm_num at this

/-- Powers of ζ₁₀ reduce modulo 10. -/
lemma zeta10_pow_reduce (n : ℕ) : ζ₁₀ ^ n = ζ₁₀ ^ (n % 10) := by
  conv_lhs => rw [← Nat.div_add_mod n 10]
  rw [pow_add, pow_mul]
  simp [zeta10_pow_ten]

/-- The norm of any power of ζ₁₀ equals 1. -/
@[simp] lemma zeta10_abs_pow (n : ℕ) : ‖ζ₁₀^n‖ = 1 := by
  rw [Complex.norm_pow, zeta10_abs, one_pow]

/-- The complex conjugate of ζ₁₀ equals ζ₁₀⁹ = ζ₁₀⁻¹. -/
@[simp] lemma zeta10_conj : starRingEnd ℂ ζ₁₀ = ζ₁₀^9 := by
  have h10 : ζ₁₀ ^ 10 = 1 := zeta10_pow_ten
  unfold ζ₁₀
  rw [← Complex.exp_conj]
  rw [map_div₀, map_mul, map_mul]
  simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [show (2 * ↑π * -I / 10 : ℂ) = -(2 * ↑π * I / 10) by ring]
  rw [Complex.exp_neg, ← Complex.exp_nat_mul]
  norm_num
  field_simp [Complex.exp_ne_zero]
  unfold ζ₁₀ at h10
  rw [← Complex.exp_nat_mul] at h10
  ring_nf at h10 ⊢
  rw [← Complex.exp_add]
  convert h10.symm using 2
  ring

/-- The multiplicative inverse of ζ₁₀ equals ζ₁₀⁹. -/
@[simp] lemma zeta10_inv_eq_pow9 : ζ₁₀⁻¹ = ζ₁₀^9 := by
  have h1 : ζ₁₀^10 = 1 := zeta10_pow_ten
  field_simp [zeta10_ne_zero]
  rw [← h1]

/-! ### Power Reduction Lemmas

These simp lemmas reduce powers of ζ₁₀ modulo 10. -/

@[simp] lemma zeta10_pow_eleven : ζ₁₀^11 = ζ₁₀ := by
  have := zeta10_pow_reduce 11; norm_num at this; exact this

@[simp] lemma zeta10_pow_twelve : ζ₁₀^12 = ζ₁₀^2 := by
  have := zeta10_pow_reduce 12; norm_num at this; exact this

@[simp] lemma zeta10_pow_thirteen : ζ₁₀^13 = ζ₁₀^3 := by
  have := zeta10_pow_reduce 13; norm_num at this; exact this

@[simp] lemma zeta10_pow_fourteen : ζ₁₀^14 = ζ₁₀^4 := by
  have := zeta10_pow_reduce 14; norm_num at this; exact this

@[simp] lemma zeta10_pow_fifteen : ζ₁₀^15 = ζ₁₀^5 := by
  have := zeta10_pow_reduce 15; norm_num at this; exact this

@[simp] lemma zeta10_pow_sixteen : ζ₁₀^16 = ζ₁₀^6 := by
  have := zeta10_pow_reduce 16; norm_num at this; exact this

@[simp] lemma zeta10_pow_seventeen : ζ₁₀^17 = ζ₁₀^7 := by
  have := zeta10_pow_reduce 17; norm_num at this; exact this

@[simp] lemma zeta10_pow_eighteen : ζ₁₀^18 = ζ₁₀^8 := by
  have := zeta10_pow_reduce 18; norm_num at this; exact this

@[simp] lemma zeta10_pow_nineteen : ζ₁₀^19 = ζ₁₀^9 := by
  have := zeta10_pow_reduce 19; norm_num at this; exact this

@[simp] lemma zeta10_pow_twenty : ζ₁₀^20 = 1 := by
  have := zeta10_pow_reduce 20; norm_num at this; exact this

@[simp] lemma zeta10_pow_21 : ζ₁₀^21 = ζ₁₀ := by
  have := zeta10_pow_reduce 21; norm_num at this; exact this

@[simp] lemma zeta10_pow_22 : ζ₁₀^22 = ζ₁₀^2 := by
  have := zeta10_pow_reduce 22; norm_num at this; exact this

@[simp] lemma zeta10_pow_23 : ζ₁₀^23 = ζ₁₀^3 := by
  have := zeta10_pow_reduce 23; norm_num at this; exact this

@[simp] lemma zeta10_pow_24 : ζ₁₀^24 = ζ₁₀^4 := by
  have := zeta10_pow_reduce 24; norm_num at this; exact this

@[simp] lemma zeta10_pow_25 : ζ₁₀^25 = ζ₁₀^5 := by
  have := zeta10_pow_reduce 25; norm_num at this; exact this

@[simp] lemma zeta10_pow_26 : ζ₁₀^26 = ζ₁₀^6 := by
  have := zeta10_pow_reduce 26; norm_num at this; exact this

@[simp] lemma zeta10_pow_27 : ζ₁₀^27 = ζ₁₀^7 := by
  have := zeta10_pow_reduce 27; norm_num at this; exact this

@[simp] lemma zeta10_pow_28 : ζ₁₀^28 = ζ₁₀^8 := by
  have := zeta10_pow_reduce 28; norm_num at this; exact this

@[simp] lemma zeta10_pow_29 : ζ₁₀^29 = ζ₁₀^9 := by
  have := zeta10_pow_reduce 29; norm_num at this; exact this

@[simp] lemma zeta10_pow_30 : ζ₁₀^30 = 1 := by
  have := zeta10_pow_reduce 30; norm_num at this; exact this

@[simp] lemma zeta10_pow_31 : ζ₁₀^31 = ζ₁₀ := by
  have := zeta10_pow_reduce 31; norm_num at this; exact this

@[simp] lemma zeta10_pow_32 : ζ₁₀^32 = ζ₁₀^2 := by
  have := zeta10_pow_reduce 32; norm_num at this; exact this

@[simp] lemma zeta10_pow_33 : ζ₁₀^33 = ζ₁₀^3 := by
  have := zeta10_pow_reduce 33; norm_num at this; exact this

@[simp] lemma zeta10_pow_34 : ζ₁₀^34 = ζ₁₀^4 := by
  have := zeta10_pow_reduce 34; norm_num at this; exact this

@[simp] lemma zeta10_pow_35 : ζ₁₀^35 = ζ₁₀^5 := by
  have := zeta10_pow_reduce 35; norm_num at this; exact this

@[simp] lemma zeta10_pow_36 : ζ₁₀^36 = ζ₁₀^6 := by
  have := zeta10_pow_reduce 36; norm_num at this; exact this

@[simp] lemma zeta10_pow_37 : ζ₁₀^37 = ζ₁₀^7 := by
  have := zeta10_pow_reduce 37; norm_num at this; exact this

@[simp] lemma zeta10_pow_38 : ζ₁₀^38 = ζ₁₀^8 := by
  have := zeta10_pow_reduce 38; norm_num at this; exact this

@[simp] lemma zeta10_pow_39 : ζ₁₀^39 = ζ₁₀^9 := by
  have := zeta10_pow_reduce 39; norm_num at this; exact this

@[simp] lemma zeta10_pow_40 : ζ₁₀^40 = 1 := by
  have := zeta10_pow_reduce 40; norm_num at this; exact this

/-! ### Cyclotomic Identity -/

/-- The cyclotomic identity: 1 + ζ₁₀ + ζ₁₀² + ... + ζ₁₀⁹ = 0.

This is the minimal polynomial relation for the primitive 10th root of unity. -/
lemma cyclotomic10_sum : 1 + ζ₁₀ + ζ₁₀^2 + ζ₁₀^3 + ζ₁₀^4 + ζ₁₀^5 + ζ₁₀^6 + ζ₁₀^7 + ζ₁₀^8 + ζ₁₀^9 = 0 := by
  have h1 : ζ₁₀^10 = 1 := zeta10_pow_ten
  have h2 : ζ₁₀ ≠ 1 := zeta10_ne_one
  have h3 : ζ₁₀ - 1 ≠ 0 := sub_ne_zero_of_ne h2
  have h_factor : ζ₁₀^10 - 1 = (ζ₁₀ - 1) * (ζ₁₀^9 + ζ₁₀^8 + ζ₁₀^7 + ζ₁₀^6 + ζ₁₀^5 + ζ₁₀^4 + ζ₁₀^3 + ζ₁₀^2 + ζ₁₀ + 1) := by ring
  rw [h1] at h_factor
  have h_zero : (ζ₁₀ - 1) * (ζ₁₀^9 + ζ₁₀^8 + ζ₁₀^7 + ζ₁₀^6 + ζ₁₀^5 + ζ₁₀^4 + ζ₁₀^3 + ζ₁₀^2 + ζ₁₀ + 1) = 0 := by
    calc (ζ₁₀ - 1) * (ζ₁₀^9 + ζ₁₀^8 + ζ₁₀^7 + ζ₁₀^6 + ζ₁₀^5 + ζ₁₀^4 + ζ₁₀^3 + ζ₁₀^2 + ζ₁₀ + 1)
        = ζ₁₀^10 - 1 := by ring
      _ = 1 - 1 := by rw [h1]
      _ = 0 := by ring
  have : ζ₁₀^9 + ζ₁₀^8 + ζ₁₀^7 + ζ₁₀^6 + ζ₁₀^5 + ζ₁₀^4 + ζ₁₀^3 + ζ₁₀^2 + ζ₁₀ + 1 = 0 := by
    have := mul_eq_zero.mp h_zero
    cases this with
    | inl h => exact absurd h h3
    | inr h => exact h
  calc 1 + ζ₁₀ + ζ₁₀^2 + ζ₁₀^3 + ζ₁₀^4 + ζ₁₀^5 + ζ₁₀^6 + ζ₁₀^7 + ζ₁₀^8 + ζ₁₀^9
      = ζ₁₀^9 + ζ₁₀^8 + ζ₁₀^7 + ζ₁₀^6 + ζ₁₀^5 + ζ₁₀^4 + ζ₁₀^3 + ζ₁₀^2 + ζ₁₀ + 1 := by ring
    _ = 0 := this

/-- ζ₁₀^5 = -1. This is because ζ₁₀^5 = e^(πi) = -1. -/
@[simp] lemma zeta10_pow_five : ζ₁₀^5 = -1 := by
  unfold ζ₁₀
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [show (5 : ℂ) * (2 * ↑π * I / 10) = ↑π * I by ring]
  rw [Complex.exp_mul_I]
  simp only [Complex.cos_pi, Complex.sin_pi]
  ring

/-- ζ₁₀^6 = -ζ₁₀, derived from ζ₁₀^5 = -1. -/
@[simp] lemma zeta10_pow_six_eq_neg : ζ₁₀^6 = -ζ₁₀ := by
  calc ζ₁₀^6 = ζ₁₀^5 * ζ₁₀ := by ring
    _ = (-1) * ζ₁₀ := by rw [zeta10_pow_five]
    _ = -ζ₁₀ := by ring

/-- ζ₁₀^7 = -ζ₁₀^2, derived from ζ₁₀^5 = -1. -/
@[simp] lemma zeta10_pow_seven_eq_neg : ζ₁₀^7 = -ζ₁₀^2 := by
  calc ζ₁₀^7 = ζ₁₀^5 * ζ₁₀^2 := by ring
    _ = (-1) * ζ₁₀^2 := by rw [zeta10_pow_five]
    _ = -ζ₁₀^2 := by ring

/-- ζ₁₀^8 = -ζ₁₀^3, derived from ζ₁₀^5 = -1. -/
@[simp] lemma zeta10_pow_eight_eq_neg : ζ₁₀^8 = -ζ₁₀^3 := by
  calc ζ₁₀^8 = ζ₁₀^5 * ζ₁₀^3 := by ring
    _ = (-1) * ζ₁₀^3 := by rw [zeta10_pow_five]
    _ = -ζ₁₀^3 := by ring

/-- ζ₁₀^9 = -ζ₁₀^4, derived from ζ₁₀^5 = -1. -/
@[simp] lemma zeta10_pow_nine_eq_neg : ζ₁₀^9 = -ζ₁₀^4 := by
  calc ζ₁₀^9 = ζ₁₀^5 * ζ₁₀^4 := by ring
    _ = (-1) * ζ₁₀^4 := by rw [zeta10_pow_five]
    _ = -ζ₁₀^4 := by ring

/-- The 10th cyclotomic polynomial relation: ζ₁₀^4 - ζ₁₀^3 + ζ₁₀^2 - ζ₁₀ + 1 = 0.

This is the minimal polynomial for primitive 10th roots of unity.
Rearranged: ζ₁₀^4 = ζ₁₀^3 - ζ₁₀^2 + ζ₁₀ - 1. -/
lemma cyclotomic10_relation : ζ₁₀^4 - ζ₁₀^3 + ζ₁₀^2 - ζ₁₀ + 1 = 0 := by
  have h := cyclotomic10_sum
  have h5 : ζ₁₀^5 = -1 := zeta10_pow_five
  -- Using ζ₁₀^k = -ζ₁₀^(k-5) for k >= 5
  have h6 : ζ₁₀^6 = -ζ₁₀ := zeta10_pow_six_eq_neg
  have h7 : ζ₁₀^7 = -ζ₁₀^2 := zeta10_pow_seven_eq_neg
  have h8 : ζ₁₀^8 = -ζ₁₀^3 := zeta10_pow_eight_eq_neg
  have h9 : ζ₁₀^9 = -ζ₁₀^4 := zeta10_pow_nine_eq_neg
  -- Substitute into 1 + ζ₁₀ + ζ₁₀^2 + ... + ζ₁₀^9 = 0
  calc ζ₁₀^4 - ζ₁₀^3 + ζ₁₀^2 - ζ₁₀ + 1
      = (1 + ζ₁₀ + ζ₁₀^2 + ζ₁₀^3 + ζ₁₀^4 + ζ₁₀^5 + ζ₁₀^6 + ζ₁₀^7 + ζ₁₀^8 + ζ₁₀^9) / 2 := by
        rw [h5, h6, h7, h8, h9]; ring
    _ = 0 / 2 := by rw [h]
    _ = 0 := by ring

/-- ζ₁₀^4 expressed in terms of lower powers. -/
lemma zeta10_pow_four_eq : ζ₁₀^4 = ζ₁₀^3 - ζ₁₀^2 + ζ₁₀ - 1 := by
  have h := cyclotomic10_relation
  linarith

/-! ### Trigonometric Values

The real and imaginary parts of powers of ζ₁₀ involve cos(kπ/5) and sin(kπ/5). -/

/-- cos(π/5) = (1 + √5)/4 = φ/2 -/
lemma cos_pi_fifth : Real.cos (π / 5) = φ / 2 := by
  rw [Real.cos_pi_div_five]
  unfold φ Real.goldenRatio
  ring

/-- cos(2π/10) = cos(π/5) = φ/2 -/
lemma cos_two_pi_tenth : Real.cos (2 * π / 10) = φ / 2 := by
  rw [show (2 * π / 10 : ℝ) = π / 5 by ring]
  exact cos_pi_fifth

/-- The real part of ζ₁₀ equals cos(π/5) = φ/2. -/
lemma zeta10_re_eq_cos : ζ₁₀.re = Real.cos (π / 5) := by
  unfold ζ₁₀
  rw [show (2 : ℂ) * π * I / 10 = (2 * π / 10 : ℝ) * I by simp [div_eq_mul_inv]; ring]
  rw [Complex.exp_ofReal_mul_I_re]
  rw [show (2 * π / 10 : ℝ) = π / 5 by ring]

/-- The real part of ζ₁₀ equals φ/2. -/
@[simp] lemma zeta10_re : ζ₁₀.re = φ / 2 := by
  rw [zeta10_re_eq_cos, cos_pi_fifth]

/-- The imaginary part of ζ₁₀ equals sin(π/5). -/
@[simp] lemma zeta10_im_eq_sin : ζ₁₀.im = Real.sin (π / 5) := by
  unfold ζ₁₀
  rw [show (2 : ℂ) * π * I / 10 = (2 * π / 10 : ℝ) * I by simp [div_eq_mul_inv]; ring]
  rw [Complex.exp_ofReal_mul_I_im]
  rw [show (2 * π / 10 : ℝ) = π / 5 by ring]

/-! ### Critical Radius -/

/-- 4 - φ is positive, ensuring r_crit_10 is well-defined.

Since φ ≈ 1.618, we have 4 - φ ≈ 2.382 > 0. -/
lemma four_minus_phi_pos : 0 < 4 - φ := by
  unfold φ
  have h := Real.goldenRatio_pos
  have h2 : Real.goldenRatio < 2 := by
    unfold Real.goldenRatio
    have : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 3)]
      norm_num
    linarith
  linarith

/-- The critical radius r_crit_10 = √(4 - φ) ≈ 1.543.

At this radius, the induced IET on segment E'₁₀E₁₀ is a 2-interval exchange
with irrational rotation number 1/φ, producing infinite orbits. -/
noncomputable def r_crit_10 : ℝ := Real.sqrt (4 - φ)

/-- The critical radius is positive. -/
lemma r_crit_10_pos : 0 < r_crit_10 := Real.sqrt_pos.mpr four_minus_phi_pos

/-- r_crit_10² = 4 - φ -/
@[simp] lemma r_crit_10_sq : r_crit_10 ^ 2 = 4 - φ :=
  Real.sq_sqrt (le_of_lt four_minus_phi_pos)

end TDCSG.GG10
