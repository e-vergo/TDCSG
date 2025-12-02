import TDCSG.Definitions.Points
import TDCSG.Proofs.Zeta5

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (psi t_F E E' F G ζ₅ zeta5 zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

lemma E_re : E.re = Real.sqrt 5 / 2 := by
  unfold E
  simp only [Complex.sub_re]

  have h4 : (ζ₅^4).re = ζ₅.re := by
    have hconj : ζ₅^4 = starRingEnd ℂ ζ₅ := zeta5_conj.symm
    rw [hconj]
    rfl
  have h3 : (ζ₅^3).re = (ζ₅^2).re := by
    have hconj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
      rw [map_pow, zeta5_conj]
      rw [show (ζ₅^4)^2 = ζ₅^8 by ring, show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta5_pow_five, one_mul]
    rw [hconj]
    rfl

  calc (ζ₅^4).re - (ζ₅^3).re
      = ζ₅.re - (ζ₅^2).re := by rw [h4, h3]
    _ = Real.sqrt 5 / 2 := by rw [zeta5_re, zeta5_sq_re]; ring

lemma E_im : E.im = Real.sin (4 * π / 5) - Real.sin (2 * π / 5) := by
  unfold E
  simp only [Complex.sub_im]

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

  calc (ζ₅^4).im - (ζ₅^3).im
      = -ζ₅.im - -(ζ₅^2).im := by rw [h4, h3]
    _ = (ζ₅^2).im - ζ₅.im := by ring
    _ = Real.sin (4 * π / 5) - Real.sin (2 * π / 5) := by rw [h2_im, zeta5_im_eq_sin]

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

lemma sqrt5_gt_one : 1 < Real.sqrt 5 := by
  have : (1 : ℝ) ^ 2 < 5 := by norm_num
  calc 1 = Real.sqrt (1 ^ 2) := by simp
       _ < Real.sqrt 5 := by
           apply Real.sqrt_lt_sqrt
           · norm_num
           · exact this

lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have : (5 : ℝ) < 3 ^ 2 := by norm_num
  calc Real.sqrt 5 < Real.sqrt (3 ^ 2) := by
           apply Real.sqrt_lt_sqrt
           · norm_num
           · exact this
       _ = 3 := by simp

lemma psi_eq : psi = (Real.sqrt 5 - 1) / 2 := by
  unfold psi Real.goldenConj
  ring

lemma psi_pos : 0 < psi := neg_pos.mpr Real.goldenConj_neg

lemma psi_ne_zero : psi ≠ 0 := ne_of_gt psi_pos

lemma psi_lt_one : psi < 1 := by
  rw [psi_eq]
  have h : Real.sqrt 5 < 3 := sqrt5_lt_three
  linarith

lemma psi_le_one : psi ≤ 1 := le_of_lt psi_lt_one

lemma psi_lt_t_F : psi < t_F := by
  rw [psi_eq]
  unfold t_F
  have sqrt5_bound : Real.sqrt 5 < 3 := sqrt5_lt_three
  rw [show (Real.sqrt 5 - 1) / 2 < (1 + Real.sqrt 5) / 4 ↔
           4 * ((Real.sqrt 5 - 1) / 2) < 4 * ((1 + Real.sqrt 5) / 4) by
      constructor <;> intro h <;> nlinarith [h]]
  field_simp
  linarith

lemma t_F_lt_one : t_F < 1 := by
  unfold t_F
  rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
  calc 1 + Real.sqrt 5
      < 1 + 3 := by linarith [sqrt5_lt_three]
    _ = 4 := by norm_num

lemma zeta5_plus_zeta5_fourth : ζ₅ + ζ₅^4 = psi := by

  conv_lhs => rw [show ζ₅^4 = starRingEnd ℂ ζ₅ from zeta5_conj.symm]
  have h1 : ζ₅ + starRingEnd ℂ ζ₅ = (2 * ζ₅.re : ℝ) := Complex.add_conj ζ₅
  rw [h1]
  have h2 : ζ₅.re = Real.cos (2 * π / 5) := by
    have h := zeta5_eq
    rw [h]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2, cos_two_pi_fifth]
  rw [psi_eq]
  unfold Real.goldenRatio
  push_cast
  ring

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

private lemma one_eq_phi_times_E_plus_zeta5_sq :
    (1 : ℂ) = Real.goldenRatio • E + ζ₅^2 := by
  unfold E

  have factorization : (psi : ℂ) • (ζ₅^4 - ζ₅^3) = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 := by
    have h1 := zeta5_plus_zeta5_fourth

    have h_mult : (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) = ζ₅^5 - ζ₅^4 + ζ₅^8 - ζ₅^7 := by ring
    rw [zeta5_pow_five] at h_mult
    have h7 : ζ₅^7 = ζ₅^2 := by
      calc ζ₅^7 = ζ₅^5 * ζ₅^2 := by ring
        _ = 1 * ζ₅^2 := by rw [zeta5_pow_five]
        _ = ζ₅^2 := by ring
    have h8 : ζ₅^8 = ζ₅^3 := by
      calc ζ₅^8 = ζ₅^5 * ζ₅^3 := by ring
        _ = 1 * ζ₅^3 := by rw [zeta5_pow_five]
        _ = ζ₅^3 := by ring
    rw [h7, h8] at h_mult
    rw [h1] at h_mult
    rw [show (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 by ring] at h_mult

    rw [← smul_eq_mul] at h_mult
    exact h_mult

  calc (1 : ℂ)
      = (ζ₅^4 - ζ₅^3) + (1 - ζ₅^4 + ζ₅^3 - ζ₅^2) + ζ₅^2 := by ring
    _ = (ζ₅^4 - ζ₅^3) + (psi : ℂ) • (ζ₅^4 - ζ₅^3) + ζ₅^2 := by
        rw [← factorization]
    _ = (1 : ℂ) • (ζ₅^4 - ζ₅^3) + (psi : ℂ) • (ζ₅^4 - ζ₅^3) + ζ₅^2 := by
        simp only [one_smul]
    _ = ((1 : ℂ) + (psi : ℂ)) • (ζ₅^4 - ζ₅^3) + ζ₅^2 := by
        rw [← add_smul]
    _ = (((1 : ℝ) + psi) : ℂ) • (ζ₅^4 - ζ₅^3) + ζ₅^2 := by
        congr 1
    _ = (Real.goldenRatio : ℂ) • (ζ₅^4 - ζ₅^3) + ζ₅^2 := by
        simp only [goldenRatio_eq_one_add_psi]
        norm_cast

lemma F_eq_psi_times_E : F = psi • E := by
  unfold F E

  have h1 := zeta5_plus_zeta5_fourth

  have h_mult : (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) = ζ₅^5 - ζ₅^4 + ζ₅^8 - ζ₅^7 := by ring
  rw [zeta5_pow_five] at h_mult
  have h7 : ζ₅^7 = ζ₅^2 := by
    calc ζ₅^7 = ζ₅^5 * ζ₅^2 := by ring
      _ = 1 * ζ₅^2 := by rw [zeta5_pow_five]
      _ = ζ₅^2 := by ring
  have h8 : ζ₅^8 = ζ₅^3 := by
    calc ζ₅^8 = ζ₅^5 * ζ₅^3 := by ring
      _ = 1 * ζ₅^3 := by rw [zeta5_pow_five]
      _ = ζ₅^3 := by ring
  rw [h7, h8] at h_mult
  rw [h1] at h_mult
  rw [show (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 by ring] at h_mult

  rw [← smul_eq_mul] at h_mult
  exact h_mult.symm

lemma F_on_segment_E'E :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ F = E' + t • (E - E') := by
  use t_F
  constructor
  ·
    unfold t_F
    apply div_nonneg
    · linarith [sqrt5_gt_one]
    · norm_num
  constructor
  ·
    exact t_F_lt_one.le
  ·
    unfold E'
    rw [show E - (-E) = 2 • E by simp [two_smul]]

    have step1 : t_F • ((2 : ℕ) • E) = (t_F * (2 : ℝ)) • E := by
      rw [show (2 : ℕ) • E = ((2 : ℝ) • E) by norm_cast]
      rw [mul_smul]
    rw [step1]

    rw [show -E + (t_F * (2 : ℝ)) • E = ((2 * t_F - 1) • E) by
      rw [← neg_one_smul ℝ E, ← add_smul, mul_comm t_F 2, show (-1 : ℝ) + 2 * t_F = 2 * t_F - 1 by ring]]

    have h_param : 2 * t_F - 1 = psi := by
      unfold t_F psi
      field_simp
      ring
    rw [h_param]
    exact F_eq_psi_times_E

lemma G_eq_coeff_times_E : G = ((Real.sqrt 5 - 2) : ℝ) • E := by

  unfold G
  rw [F_eq_psi_times_E]

  have h_coeff : 2 * psi - 1 = Real.sqrt 5 - 2 := by
    rw [psi_eq]
    field_simp
    ring

  have h_smul : (2 : ℂ) * psi • E = ((2 : ℝ) * psi) • E := by
    rw [mul_smul]
    simp [ofReal_ofNat]
  rw [h_smul]

  rw [show E = (1 : ℝ) • E by simp]
  simp only [smul_smul, mul_one]
  rw [← sub_smul]
  rw [h_coeff]

end TDCSG.CompoundSymmetry.GG5
