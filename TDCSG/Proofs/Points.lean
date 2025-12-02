/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Points
import TDCSG.Proofs.Zeta5

/-!
# Geometric Points for the GG5 Construction

This file proves properties of the key geometric points E and E' used in the GG5
construction, including their positions relative to the disk boundaries.

## Main results

- `E_on_left_disk_boundary`: Point E lies on the boundary of the left disk
- `E_in_right_disk`: Point E lies inside the right disk

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (E E' psi t_G ζ₅ zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

private lemma E_plus_one_re : (E + 1).re = 1 + Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
  unfold E
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re]

  have h4 : (ζ₅^4).re = ζ₅.re := by
    have hconj : ζ₅^4 = starRingEnd ℂ ζ₅ := zeta5_conj.symm
    rw [hconj]; rfl
  have h3 : (ζ₅^3).re = (ζ₅^2).re := by
    have hconj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
      rw [map_pow, zeta5_conj]
      rw [show (ζ₅^4)^2 = ζ₅^8 by ring, show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta5_pow_five, one_mul]
    rw [hconj]; rfl

  calc (ζ₅^4).re - (ζ₅^3).re + 1
      = ζ₅.re - (ζ₅^2).re + 1 := by rw [h4, h3]
    _ = 1 + Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
        rw [zeta5_re, zeta5_sq_re, cos_two_pi_fifth, cos_four_pi_fifth, Real.cos_pi_div_five]
        unfold Real.goldenRatio
        field_simp
        ring

private lemma E_plus_one_im : (E + 1).im = Real.sin (4 * π / 5) - Real.sin (2 * π / 5) := by
  unfold E
  simp only [Complex.add_im, Complex.sub_im, Complex.one_im]

  have h4 : (ζ₅^4).im = -ζ₅.im := by
    have hconj : ζ₅^4 = starRingEnd ℂ ζ₅ := zeta5_conj.symm
    rw [hconj]
    exact Complex.conj_im ζ₅
  have h3 : (ζ₅^3).im = -(ζ₅^2).im := by
    have hconj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
      rw [map_pow, zeta5_conj]
      rw [show (ζ₅^4)^2 = ζ₅^8 by ring, show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta5_pow_five, one_mul]
    rw [hconj]
    exact Complex.conj_im (ζ₅^2)
  have h2_im : (ζ₅^2).im = Real.sin (4 * π / 5) := by
    have h2 := zeta5_sq_eq
    rw [h2]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

  calc (ζ₅^4).im - (ζ₅^3).im + 0
      = -ζ₅.im - -(ζ₅^2).im := by rw [h4, h3]; ring
    _ = (ζ₅^2).im - ζ₅.im := by ring
    _ = Real.sin (4 * π / 5) - Real.sin (2 * π / 5) := by rw [h2_im, zeta5_im_eq_sin]

private lemma sin_two_pi_fifth : Real.sin (2 * π / 5) = 2 * Real.sin (π / 5) * Real.cos (π / 5) := by
  rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring]
  exact Real.sin_two_mul (π / 5)

lemma E_on_left_disk_boundary : ‖E + 1‖ = r_crit := by
  have h_sq : ‖E + 1‖ ^ 2 = 3 + Real.goldenRatio := by
    unfold E
    rw [Complex.sq_norm, Complex.normSq_apply, show (ζ₅^4 - ζ₅^3 + 1 : ℂ) = E + 1 by unfold E; ring]
    rw [E_plus_one_re, E_plus_one_im]

    rw [cos_four_pi_fifth, sin_four_pi_fifth]
    rw [cos_two_pi_fifth, Real.cos_pi_div_five, sin_two_pi_fifth]
    unfold Real.goldenRatio
    have h_re : (1 + ((1 + Real.sqrt 5) / 2 - 1) / 2 - -((1 + Real.sqrt 5) / 4)) =
                (2 + Real.sqrt 5) / 2 := by field_simp; ring
    rw [h_re]
    have h_im_factor : (2 * Real.cos (π / 5) - 1) = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.cos_pi_div_five]; field_simp; ring

    have h_im : (Real.sin (π / 5) - 2 * Real.sin (π / 5) * Real.cos (π / 5)) =
                -(Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) := by
      have h_orig : (2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5)) =
                    Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2 := by
        rw [show 2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5) =
                Real.sin (π / 5) * (2 * Real.cos (π / 5) - 1) by ring, h_im_factor]
        ring
      linarith
    rw [h_im]

    rw [neg_mul_neg]
    have h_sin_sq : Real.sin (π / 5) ^ 2 = 1 - ((1 + Real.sqrt 5) / 4) ^ 2 := by
      have h := Real.sin_sq_add_cos_sq (π / 5)
      rw [Real.cos_pi_div_five] at h
      linarith
    rw [show (2 + Real.sqrt 5) / 2 * ((2 + Real.sqrt 5) / 2) +
              Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2 * (Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) =
              ((2 + Real.sqrt 5) / 2) ^ 2 + (Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) ^ 2 by ring]
    rw [show (Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) ^ 2 =
              Real.sin (π / 5) ^ 2 * ((Real.sqrt 5 - 1) / 2) ^ 2 by ring, h_sin_sq]
    field_simp
    calc (2 + Real.sqrt 5) ^ 2 * 4 ^ 2 + (4 ^ 2 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2
        = (2 + Real.sqrt 5) ^ 2 * 16 + (16 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2 := by norm_num
      _ = (4 + 4 * Real.sqrt 5 + Real.sqrt 5 ^ 2) * 16 +
          (16 - 1 - 2 * Real.sqrt 5 - Real.sqrt 5 ^ 2) * (Real.sqrt 5 ^ 2 - 2 * Real.sqrt 5 + 1) := by ring
      _ = (4 + 4 * Real.sqrt 5 + 5) * 16 +
          (16 - 1 - 2 * Real.sqrt 5 - 5) * (5 - 2 * Real.sqrt 5 + 1) := by rw [sqrt5_sq]
      _ = (9 + 4 * Real.sqrt 5) * 16 + (10 - 2 * Real.sqrt 5) * (6 - 2 * Real.sqrt 5) := by ring
      _ = 144 + 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * Real.sqrt 5 ^ 2 := by ring
      _ = 144 + 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * 5 := by rw [sqrt5_sq]
      _ = 144 + 60 + 20 + 64 * Real.sqrt 5 - 32 * Real.sqrt 5 := by ring
      _ = 224 + 32 * Real.sqrt 5 := by ring
      _ = 2 * 16 * (6 + (1 + Real.sqrt 5)) := by ring
      _ = 2 * 4 ^ 2 * (2 * 3 + (1 + Real.sqrt 5)) := by norm_num
  rw [← Real.sqrt_sq (norm_nonneg (E + 1)), h_sq]

  rfl

private lemma E_minus_one_re : (E - 1).re = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) - 1 := by
  unfold E
  simp only [Complex.sub_re, Complex.one_re]

  have h4 : (ζ₅^4).re = ζ₅.re := by
    have hconj : ζ₅^4 = starRingEnd ℂ ζ₅ := zeta5_conj.symm
    rw [hconj]; rfl
  have h3 : (ζ₅^3).re = (ζ₅^2).re := by
    have hconj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
      rw [map_pow, zeta5_conj]
      rw [show (ζ₅^4)^2 = ζ₅^8 by ring, show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta5_pow_five, one_mul]
    rw [hconj]; rfl

  calc (ζ₅^4).re - (ζ₅^3).re - 1
      = ζ₅.re - (ζ₅^2).re - 1 := by rw [h4, h3]
    _ = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) - 1 := by
        rw [zeta5_re, zeta5_sq_re, cos_two_pi_fifth, cos_four_pi_fifth, Real.cos_pi_div_five]
        unfold Real.goldenRatio
        field_simp
        ring

private lemma E_minus_one_im : (E - 1).im = Real.sin (4 * π / 5) - Real.sin (2 * π / 5) := by
  unfold E
  simp only [Complex.sub_im, Complex.one_im]

  have h4 : (ζ₅^4).im = -ζ₅.im := by
    have hconj : ζ₅^4 = starRingEnd ℂ ζ₅ := zeta5_conj.symm
    rw [hconj]
    exact Complex.conj_im ζ₅
  have h3 : (ζ₅^3).im = -(ζ₅^2).im := by
    have hconj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
      rw [map_pow, zeta5_conj]
      rw [show (ζ₅^4)^2 = ζ₅^8 by ring, show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta5_pow_five, one_mul]
    rw [hconj]
    exact Complex.conj_im (ζ₅^2)
  have h2_im : (ζ₅^2).im = Real.sin (4 * π / 5) := by
    have h2 := zeta5_sq_eq
    rw [h2]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

  calc (ζ₅^4).im - (ζ₅^3).im - 0
      = -ζ₅.im - -(ζ₅^2).im := by rw [h4, h3]; ring
    _ = (ζ₅^2).im - ζ₅.im := by ring
    _ = Real.sin (4 * π / 5) - Real.sin (2 * π / 5) := by rw [h2_im, zeta5_im_eq_sin]

lemma E_in_right_disk : ‖E - 1‖ ≤ r_crit := by

  have h_sq : ‖E - 1‖ ^ 2 < 3 + Real.goldenRatio := by
    unfold E
    rw [Complex.sq_norm, Complex.normSq_apply, show (ζ₅^4 - ζ₅^3 - 1 : ℂ) = E - 1 by unfold E; ring]
    rw [E_minus_one_re, E_minus_one_im]

    rw [cos_four_pi_fifth, sin_four_pi_fifth]
    rw [cos_two_pi_fifth, Real.cos_pi_div_five, sin_two_pi_fifth]
    unfold Real.goldenRatio

    have h_re : (((1 + Real.sqrt 5) / 2 - 1) / 2 - -((1 + Real.sqrt 5) / 4) - 1) =
                (Real.sqrt 5 - 2) / 2 := by field_simp; ring
    rw [h_re]

    have h_im_factor : (2 * Real.cos (π / 5) - 1) = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.cos_pi_div_five]; field_simp; ring
    have h_im : (Real.sin (π / 5) - 2 * Real.sin (π / 5) * Real.cos (π / 5)) =
                -(Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) := by
      have h_orig : (2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5)) =
                    Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2 := by
        rw [show 2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5) =
                Real.sin (π / 5) * (2 * Real.cos (π / 5) - 1) by ring, h_im_factor]
        ring
      linarith
    rw [h_im]

    rw [neg_mul_neg]
    have h_sin_sq : Real.sin (π / 5) ^ 2 = 1 - ((1 + Real.sqrt 5) / 4) ^ 2 := by
      have h := Real.sin_sq_add_cos_sq (π / 5)
      rw [Real.cos_pi_div_five] at h
      linarith
    rw [show (Real.sqrt 5 - 2) / 2 * ((Real.sqrt 5 - 2) / 2) +
              Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2 * (Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) =
              ((Real.sqrt 5 - 2) / 2) ^ 2 + (Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) ^ 2 by ring]
    rw [show (Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2) ^ 2 =
              Real.sin (π / 5) ^ 2 * ((Real.sqrt 5 - 1) / 2) ^ 2 by ring, h_sin_sq]
    field_simp
    have h_calc : (Real.sqrt 5 - 2) ^ 2 * 4 ^ 2 + (4 ^ 2 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2
                  = 224 - 96 * Real.sqrt 5 := by
      calc (Real.sqrt 5 - 2) ^ 2 * 4 ^ 2 + (4 ^ 2 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2
          = (Real.sqrt 5 - 2) ^ 2 * 16 + (16 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2 := by norm_num
        _ = (Real.sqrt 5 ^ 2 - 4 * Real.sqrt 5 + 4) * 16 +
            (16 - 1 - 2 * Real.sqrt 5 - Real.sqrt 5 ^ 2) * (Real.sqrt 5 ^ 2 - 2 * Real.sqrt 5 + 1) := by ring
        _ = (5 - 4 * Real.sqrt 5 + 4) * 16 +
            (16 - 1 - 2 * Real.sqrt 5 - 5) * (5 - 2 * Real.sqrt 5 + 1) := by rw [sqrt5_sq]
        _ = (9 - 4 * Real.sqrt 5) * 16 + (10 - 2 * Real.sqrt 5) * (6 - 2 * Real.sqrt 5) := by ring
        _ = 144 - 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * Real.sqrt 5 ^ 2 := by ring
        _ = 144 - 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * 5 := by rw [sqrt5_sq]
        _ = 144 + 60 + 20 - 96 * Real.sqrt 5 := by ring
        _ = 224 - 96 * Real.sqrt 5 := by ring
    rw [h_calc]

    have h_target : 2 * 4 ^ 2 * (2 * 3 + (1 + Real.sqrt 5)) = 224 + 32 * Real.sqrt 5 := by norm_num; ring
    rw [h_target]

    have : 0 < 128 * Real.sqrt 5 := by
      apply mul_pos
      · norm_num
      · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
    linarith
  have h_pos : 0 < 3 + Real.goldenRatio := by linarith [Real.goldenRatio_pos]
  have : ‖E - 1‖ < r_crit := by
    calc ‖E - 1‖
        = Real.sqrt (‖E - 1‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ < Real.sqrt (3 + Real.goldenRatio) := by
          apply Real.sqrt_lt_sqrt (sq_nonneg _) h_sq
      _ = r_crit := by unfold r_crit; rfl
  exact this.le

private lemma zeta5_sq_plus_zeta5_cube : ζ₅^2 + ζ₅^3 = -Real.goldenRatio := by

  have h_conj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
    rw [map_pow, zeta5_conj]
    rw [show (ζ₅ ^ 4) ^ 2 = ζ₅^8 by ring]
    rw [show (8 : ℕ) = 5 + 3 by norm_num]
    rw [pow_add, zeta5_pow_five, one_mul]
  rw [h_conj]
  have h_real : ζ₅^2 + starRingEnd ℂ (ζ₅^2) = (2 * (ζ₅^2).re : ℝ) := Complex.add_conj (ζ₅^2)
  rw [h_real]
  have h2 : (ζ₅^2).re = Real.cos (4 * π / 5) := by
    have h := zeta5_sq_eq
    rw [h]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2]
  rw [cos_four_pi_fifth, Real.cos_pi_div_five]
  unfold Real.goldenRatio
  push_cast
  ring

private lemma goldenRatio_eq_one_add_psi : Real.goldenRatio = 1 + psi := by
  unfold Real.goldenRatio psi
  field_simp
  ring

end TDCSG.CompoundSymmetry.GG5
