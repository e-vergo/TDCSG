import TDCSG.Definitions.Core
import TDCSG.MainTheorem
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Isometry

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (ζ₅ zeta5 zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

@[simp] lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

lemma three_plus_phi_pos : 0 < 3 + φ := by
  unfold φ
  have := Real.goldenRatio_pos
  linarith

lemma one_plus_phi_pos : 0 < 1 + φ := by
  unfold φ
  linarith [Real.goldenRatio_pos]

lemma one_plus_phi_ne_zero : 1 + φ ≠ 0 := ne_of_gt one_plus_phi_pos

lemma phi_ne_zero : φ ≠ 0 := ne_of_gt (by unfold φ; exact Real.goldenRatio_pos)

@[simp] lemma zeta5_pow_five : ζ₅ ^ 5 = 1 := by
  unfold ζ₅ zeta5
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  ring

@[simp] lemma zeta5_pow_zero : ζ₅ ^ 0 = 1 := pow_zero ζ₅

@[simp] lemma zeta5_pow_zero_re : (ζ₅ ^ 0).re = 1 := by simp

@[simp] lemma zeta5_pow_zero_im : (ζ₅ ^ 0).im = 0 := by simp

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

@[simp] lemma zeta5_abs : ‖ζ₅‖ = 1 := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]
    ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * π / 5)

@[simp] lemma zeta5_abs_pow (n : ℕ) : ‖ζ₅^n‖ = 1 := by
  rw [Complex.norm_pow, zeta5_abs, one_pow]

lemma zeta5_abs_pow4 : ‖ζ₅^4‖ = 1 := zeta5_abs_pow 4

lemma zeta5_isPrimitiveRoot : IsPrimitiveRoot ζ₅ 5 := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = 2 * π * I / (5 : ℂ) by norm_cast]
  exact Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma zeta5_pow_ne_one {k : ℕ} (hk : k ≠ 0) (hk5 : k < 5) : ζ₅ ^ k ≠ 1 :=
  zeta5_isPrimitiveRoot.pow_ne_one_of_pos_of_lt hk hk5

lemma zeta5_pow_eq_one_iff {k : ℕ} : ζ₅ ^ k = 1 ↔ 5 ∣ k := by
  exact zeta5_isPrimitiveRoot.pow_eq_one_iff_dvd k

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

lemma zeta5_mul_inv : ζ₅ * ζ₅⁻¹ = 1 := by
  field_simp [zeta5_ne_zero]

lemma zeta5_inv_as_pow4 : ζ₅⁻¹ = ζ₅^4 := zeta5_inv_eq_pow4

lemma zeta5_pow_mul_inv (n : ℕ) : ζ₅^n * ζ₅⁻¹ = ζ₅^((n + 4) % 5) := by
  rw [zeta5_inv_as_pow4]
  rw [← pow_add]
  exact zeta5_pow_reduce (n + 4)

lemma zeta5_inv_mul_pow (n : ℕ) : ζ₅⁻¹ * ζ₅^n = ζ₅^((n + 4) % 5) := by
  rw [mul_comm]
  exact zeta5_pow_mul_inv n

lemma zeta5_sq_mul_inv : ζ₅^2 * ζ₅⁻¹ = ζ₅ := by
  rw [zeta5_inv_eq_pow4, ← pow_add]
  norm_num [zeta5_pow_reduce 6]

lemma zeta5_pow4_mul_sq : ζ₅^4 * ζ₅^2 = ζ₅ := by
  rw [← pow_add]
  have : ζ₅^6 = ζ₅^(6 % 5) := zeta5_pow_reduce 6
  norm_num at this
  exact this

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

lemma zeta5_pow4_eq : ζ₅^4 = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by
  have h := cyclotomic5_sum

  have h2 : ζ₅^4 + (1 + ζ₅ + ζ₅^2 + ζ₅^3) = 0 := by
    calc ζ₅^4 + (1 + ζ₅ + ζ₅^2 + ζ₅^3)
        = 1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 := by ring
      _ = 0 := h
  calc ζ₅^4 = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + (ζ₅^4 + (1 + ζ₅ + ζ₅^2 + ζ₅^3)) := by ring
    _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + 0 := by rw [h2]
    _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) := by ring
    _ = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by ring

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
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]; ring]
  exact Complex.exp_ofReal_mul_I_re (2 * π / 5)

@[simp] lemma zeta5_im_eq_sin : ζ₅.im = Real.sin (2 * π / 5) := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]; ring]
  exact Complex.exp_ofReal_mul_I_im (2 * π / 5)

lemma zeta5_eq : ζ₅ = ↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5)) := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by push_cast; field_simp]
  rw [Complex.exp_mul_I,  Complex.ofReal_cos, Complex.ofReal_sin]
  ring

lemma zeta5_sq_eq : ζ₅^2 = ↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5)) := by
  unfold ζ₅ zeta5
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

lemma zeta5_im_pos : 0 < ζ₅.im := by
  rw [zeta5_im_eq_sin]
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

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

lemma zeta5_sq_re_eq_phi : (ζ₅^2).re = -Real.goldenRatio / 2 := by
  rw [zeta5_sq_re]
  unfold Real.goldenRatio
  ring

lemma zeta5_cubed_eq : ζ₅^3 = Complex.exp ((6 * π / 5 : ℝ) * I) := by
  unfold ζ₅ zeta5
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

lemma sin_eight_pi_fifth : Real.sin (8 * π / 5) = -Real.sin (2 * π / 5) := by
  rw [show (8 * π / 5 : ℝ) = 2 * π - 2 * π / 5 by ring]
  rw [Real.sin_two_pi_sub]

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

lemma zeta5_pow4_im_neg' : (ζ₅^4).im < 0 := by
  rw [zeta5_pow4_im]
  apply neg_neg_of_pos
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

lemma zeta5_sq_im_pos : 0 < (ζ₅^2).im := by
  rw [zeta5_sq_im_eq]
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

lemma one_add_zeta5_pow4_re : (1 + ζ₅^4).re = 1 + (Real.sqrt 5 - 1) / 4 := by
  simp only [Complex.add_re, Complex.one_re, zeta5_pow4_re]

lemma one_sub_zeta5_pow4_re : (1 - ζ₅^4).re = 1 - (Real.sqrt 5 - 1) / 4 := by
  simp only [Complex.sub_re, Complex.one_re, zeta5_pow4_re]

lemma zeta5_powers_re_sum : ζ₅.re + (ζ₅^2).re + (ζ₅^3).re + (ζ₅^4).re = -1 := by
  have h := cyclotomic5_sum
  have h_re := congr_arg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h_re
  linarith

export TDCSG.Definitions (zeta5Circle zeta5Circle_coe zeta5CirclePow zeta5CircleInv zeta5CircleInv_coe)

lemma zeta5CirclePow_coe (n : ℕ) : (zeta5CirclePow n : ℂ) = ζ₅ ^ n := by
  induction n with
  | zero => simp [zeta5CirclePow]
  | succ n ih =>
    simp only [zeta5CirclePow, pow_succ, Circle.coe_mul]
    rw [← zeta5CirclePow, ih, zeta5Circle_coe]

lemma zeta5CirclePow4_eq_inv : zeta5CirclePow 4 = zeta5CircleInv := by
  apply Circle.ext
  simp only [zeta5CirclePow, zeta5CircleInv, Circle.coe_inv, zeta5Circle_coe]
  show (zeta5Circle ^ 4 : ℂ) = ζ₅⁻¹
  simp only [pow_succ, pow_zero, zeta5Circle_coe, zeta5_inv_as_pow4]

lemma circle_exp_two_pi_fifth : Circle.exp (2 * π / 5) = zeta5Circle := by
  apply Circle.ext
  simp only [Circle.coe_exp, zeta5Circle_coe]
  unfold ζ₅ zeta5
  congr 1
  push_cast
  ring

end TDCSG.CompoundSymmetry.GG5
