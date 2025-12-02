import TDCSG.Proofs.CrossDiskWord3Helpers
import TDCSG.Proofs.RotationFormulas

set_option maxHeartbeats 400000

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions

private noncomputable abbrev c_lower_word2 : ℝ := Real.goldenConj

private noncomputable abbrev c_upper_word2 : ℝ := 2 - √5

private noncomputable abbrev c_lower_word3 : ℝ := 2 - √5

lemma c_lower_word2_eq : c_lower_word2 = (1 - √5) / 2 := by
  unfold c_lower_word2 Real.goldenConj; rfl

lemma interval1_c_lower_bound (x : ℝ) (hx : length1 ≤ x) :
    (1 - √5) / 2 ≤ 2 * x - 1 := by
  have h_length1 : length1 = 1 / (2 * (1 + goldenRatio)) := rfl
  have h_goldenRatio : goldenRatio = (1 + √5) / 2 := Real.goldenRatio.eq_1
  have h_sqrt5_pos : √5 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  have h_denom_pos : 1 + goldenRatio > 0 := by
    rw [h_goldenRatio]; linarith
  have h_length1_val : 1 / (2 * (1 + goldenRatio)) = (3 - √5) / 4 := by grind
  calc 2 * x - 1 ≥ 2 * (1 / (2 * (1 + goldenRatio))) - 1 := by
        rw [← h_length1]; linarith
    _ = 2 * ((3 - √5) / 4) - 1 := by rw [h_length1_val]
    _ = (3 - √5) / 2 - 1 := by ring
    _ = (3 - √5 - 2) / 2 := by ring
    _ = (1 - √5) / 2 := by ring

lemma interval1_c_upper_bound (x : ℝ) (hx : x < length1 + length2) :
    2 * x - 1 < 2 - √5 := by
  have h_length12 : length1 + length2 = (3 - √5) / 2 := length12_eq_sqrt5
  calc 2 * x - 1 < 2 * (length1 + length2) - 1 := by linarith
    _ = 2 * ((3 - √5) / 2) - 1 := by rw [h_length12]
    _ = 3 - √5 - 1 := by ring
    _ = 2 - √5 := by ring

set_option maxHeartbeats 600000 in

lemma cross_disk_w2_z1_bound (c : ℝ) (hc_lo : (1 - √5) / 2 ≤ c) (hc_hi : c ≤ 2 - √5) :
    ‖(ζ₅^4 - 2 : ℂ) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by

  set A : ℂ := ζ₅^4 - 2 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_upper : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]
    have h_expr : (ζ₅^4 - 2 : ℂ) + ((2 - √5 : ℝ) : ℂ) * (1 - ζ₅) = ζ₅^4 - (2 - √5)*ζ₅ - √5 := by
      push_cast; ring
    rw [h_expr]
    exact normSq_w3_z1_at_lower

  have h_at_lower : ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]

    have h_expr : (ζ₅^4 - 2 : ℂ) + (((1 - √5)/2 : ℝ) : ℂ) * (1 - ζ₅) =
        ζ₅^4 - ((1 - √5)/2 : ℝ) * ζ₅ - ↑((3 + √5) / 2 : ℝ) := by
      push_cast; ring
    rw [h_expr]

    rw [Complex.normSq_apply]

    have h_re : (ζ₅^4 - ((1 - √5)/2 : ℝ) * ζ₅ - ↑((3 + √5) / 2 : ℝ) : ℂ).re = (-2 - √5) / 2 := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_pow4_re, zeta5_re, zeta5_im_eq_sin]
      ring_nf
      nlinarith [sqrt5_sq]

    have h_im : (ζ₅^4 - ((1 - √5)/2 : ℝ) * ζ₅ - ↑((3 + √5) / 2 : ℝ) : ℂ).im =
        Real.sin (2 * π / 5) * ((√5 - 3) / 2) := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_pow4_im', zeta5_im_eq_sin]
      ring
    rw [h_re, h_im]
    have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
    simp only [← sq]

    have h1 : ((-2 - √5) / 2)^2 = (9 + 4*√5) / 4 := by nlinarith [sqrt5_sq]
    have h2 : ((√5 - 3) / 2)^2 = (14 - 6*√5) / 4 := by nlinarith [sqrt5_sq]
    have h3 : (14 - 6*√5) * ((5 + √5) / 8) = (40 - 16*√5) / 8 := by nlinarith [sqrt5_sq]

    calc ((-2 - √5) / 2)^2 + (Real.sin (2 * π / 5) * ((√5 - 3) / 2))^2
        = (9 + 4*√5) / 4 + Real.sin (2 * π / 5)^2 * ((14 - 6*√5) / 4) := by
          rw [h1, mul_pow, h2]
      _ = (9 + 4*√5) / 4 + ((5 + √5) / 8) * ((14 - 6*√5) / 4) := by rw [h_sin_sq]
      _ = (9 + 4*√5) / 4 + (40 - 16*√5) / 32 := by nlinarith [sqrt5_sq]
      _ = (72 + 32*√5 + 40 - 16*√5) / 32 := by ring
      _ = (112 + 16*√5) / 32 := by ring
      _ = (7 + √5) / 2 := by ring
      _ = 3 + (1 + √5) / 2 := by ring
      _ = 3 + φ := by simp only [φ, Real.goldenRatio]
      _ ≤ 3 + φ := le_refl _

  have h_coeff_a : Complex.normSq B = (5 - √5) / 2 := by rw [hB_def]; exact normSq_B4
  have h_coeff_b : (A * starRingEnd ℂ B).re = (2*√5 - 5) / 2 := by
    rw [hA_def, hB_def]; exact re_A_w3_z1_mul_conj_B
  have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]
  have h_vertex : -(((2*√5 - 5) / 2) / ((5 - √5) / 2)) = (3 - √5) / 4 := w3_z1_vertex

  have h_sqrt5_gt_2 : √5 > 2 := by
    have : (2 : ℝ)^2 < 5 := by norm_num
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).mpr this
  have h_vertex_above : (3 - √5) / 4 > 2 - √5 := by nlinarith [sqrt5_sq, h_sqrt5_gt_2]

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

  have h_mono : ∀ c₁ c₂ : ℝ, (1 - √5) / 2 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ 2 - √5 →
      Complex.normSq (A + (c₂ : ℂ) * B) ≤ Complex.normSq (A + (c₁ : ℂ) * B) := by
    intro c₁ c₂ hc1_lo hc12 hc2_hi
    rw [h_normSq_expand c₁, h_normSq_expand c₂]

    have h_sum_bound : c₁ + c₂ ≤ 2 * (2 - √5) := by linarith

    have h_factor_neg_at_bound : 2 * ((2*√5 - 5) / 2) + 2 * (2 - √5) * ((5 - √5) / 2) ≤ 0 := by
      have h1 : 2 * ((2*√5 - 5) / 2) = 2*√5 - 5 := by ring
      have h2 : 2 * (2 - √5) * ((5 - √5) / 2) = (2 - √5) * (5 - √5) := by ring
      have h3 : (2 - √5) * (5 - √5) = 15 - 7*√5 := by nlinarith [sqrt5_sq]
      rw [h1, h2, h3]

      nlinarith [sqrt5_sq]
    have h_factor_neg : 2 * (A * starRingEnd ℂ B).re + (c₁ + c₂) * Complex.normSq B ≤ 0 := by
      rw [hA_def, hB_def, h_coeff_b, h_coeff_a]
      calc 2 * ((2*√5 - 5) / 2) + (c₁ + c₂) * ((5 - √5) / 2)
          ≤ 2 * ((2*√5 - 5) / 2) + (2 * (2 - √5)) * ((5 - √5) / 2) := by
            have h_pos : (5 - √5) / 2 > 0 := h_a_pos
            have h_ineq : (c₁ + c₂) * ((5 - √5) / 2) ≤ (2 * (2 - √5)) * ((5 - √5) / 2) := by
              apply mul_le_mul_of_nonneg_right h_sum_bound (le_of_lt h_pos)
            linarith
        _ ≤ 0 := h_factor_neg_at_bound

    rw [h_coeff_b, h_coeff_a]
    have h_diff : (6 - √5) + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2) -
                  ((6 - √5) + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2)) =
                  (c₂ - c₁) * ((2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
    have h_c_diff_nonneg : c₂ - c₁ ≥ 0 := by linarith
    have h_factor_neg' : (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
      have h := h_factor_neg
      rw [h_coeff_b, h_coeff_a] at h
      linarith
    have h_prod_nonpos : (c₂ - c₁) * ((2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h_c_diff_nonneg h_factor_neg'

    have h_normSq_A : Complex.normSq A = 6 - √5 := by rw [hA_def]; exact normSq_A_w3_z1
    rw [h_normSq_A]
    linarith [h_diff, h_prod_nonpos]

  rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]

  calc Complex.normSq ((ζ₅^4 - 2) + (c : ℂ) * (1 - ζ₅))
      ≤ Complex.normSq ((ζ₅^4 - 2) + (((1 - √5)/2 : ℝ) : ℂ) * (1 - ζ₅)) := by
        apply h_mono ((1 - √5)/2) c (le_refl _) hc_lo hc_hi
    _ ≤ 3 + φ := by rw [← hA_def, ← hB_def, Complex.normSq_eq_norm_sq]; exact h_at_lower

lemma cross_disk_w2_z2_bound (c : ℝ) (hc_lo : (1 - √5) / 2 ≤ c) (hc_hi : c ≤ 2 - √5) :
    ‖((2 : ℂ) - 2*ζ₅^4 + ζ₅^3) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by

  set A : ℂ := 2 + ζ₅^3 - 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  have h_expr_eq : ∀ t : ℝ, ((2 : ℂ) - 2*ζ₅^4 + ζ₅^3) + (t : ℂ) * (ζ₅^4 - 1) = A + (t : ℂ) * B := by
    intro t; simp only [hA_def, hB_def]; ring

  rw [h_expr_eq, show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_coeff_a : Complex.normSq B = (5 - √5) / 2 := by rw [hB_def]; exact normSq_B3
  have h_coeff_b : (A * starRingEnd ℂ B).re = (3*√5 - 10) / 2 := by
    rw [hA_def, hB_def]; exact re_A_w3_z2_mul_conj_B
  have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]
  have h_vertex : -(((3*√5 - 10) / 2) / ((5 - √5) / 2)) = (7 - √5) / 4 := w3_z2_vertex

  have h_sqrt5_gt_1 : √5 > 1 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5)
  have h_vertex_above : (7 - √5) / 4 > 2 - √5 := by nlinarith [h_sqrt5_gt_1]

  have h_at_upper : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]

    have h_match : (2 + ζ₅^3 - 2*ζ₅^4 : ℂ) + ((2 - √5 : ℝ) : ℂ) * (ζ₅^4 - 1) =
        (√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4 := by push_cast; ring
    rw [h_match]
    exact normSq_w3_z2_at_lower

  have h_at_lower : ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]

    have h_expr : (2 + ζ₅^3 - 2*ζ₅^4 : ℂ) + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1) =
        ↑((3 + √5)/2 : ℝ) + ζ₅^3 - ↑((3 + √5)/2 : ℝ) * ζ₅^4 := by push_cast; ring
    rw [h_expr, Complex.normSq_apply]

    have h_re : ((↑((3 + √5)/2 : ℝ) + ζ₅^3 - ↑((3 + √5)/2 : ℝ) * ζ₅^4) : ℂ).re =
        (3 + √5) / 2 + (-(√5 + 1) / 4) - ((3 + √5) / 2) * ((√5 - 1) / 4) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_cubed_re, zeta5_pow4_re]
      ring

    have h_im : ((↑((3 + √5)/2 : ℝ) + ζ₅^3 - ↑((3 + √5)/2 : ℝ) * ζ₅^4) : ℂ).im =
        Real.sin (π / 5) * (1 + √5) := by
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_cubed_im', zeta5_pow4_im']
      have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
        rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul, Real.cos_pi_div_five]
        ring
      rw [h_sin_double]

      have h_prod : (3 + √5) * (1 + √5) = 8 + 4*√5 := by nlinarith [sqrt5_sq]
      have h_factor : -1 + (3 + √5) * (1 + √5) / 4 = 1 + √5 := by
        rw [h_prod]; ring

      have h_goal : 0 + -Real.sin (π / 5) - ((3 + √5) / 2 * -(Real.sin (π / 5) * (1 + √5) / 2) + 0 * (ζ₅^4).re) =
          Real.sin (π / 5) * (-1 + (3 + √5) * (1 + √5) / 4) := by ring
      rw [h_goal, h_factor]
    rw [h_re, h_im]

    have h_re_val : (3 + √5) / 2 + (-(√5 + 1) / 4) - ((3 + √5) / 2) * ((√5 - 1) / 4) = 1 := by
      nlinarith [sqrt5_sq]

    have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
    have h_phi_sq : (1 + √5)^2 = 6 + 2*√5 := by nlinarith [sqrt5_sq]
    simp only [← sq]
    calc ((3 + √5) / 2 + (-(√5 + 1) / 4) - ((3 + √5) / 2) * ((√5 - 1) / 4))^2 +
        (Real.sin (π / 5) * (1 + √5))^2
        = 1 + Real.sin (π / 5)^2 * (1 + √5)^2 := by rw [h_re_val]; ring
      _ = 1 + ((5 - √5) / 8) * (6 + 2*√5) := by rw [h_sin_sq, h_phi_sq]
      _ = 1 + (30 + 10*√5 - 6*√5 - 2*5) / 8 := by nlinarith [sqrt5_sq]
      _ = 1 + (20 + 4*√5) / 8 := by ring
      _ = 1 + (5 + √5) / 2 := by ring
      _ = (7 + √5) / 2 := by ring
      _ = 3 + (1 + √5) / 2 := by ring
      _ = 3 + φ := by simp only [φ, Real.goldenRatio]
      _ ≤ 3 + φ := le_refl _

  have h_normSq_A : Complex.normSq A = 11 - 4*√5 := by rw [hA_def]; exact normSq_A_w3_z2

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
    rw [h_re_scale]; ring

  have h_mono : ∀ c₁ c₂ : ℝ, (1 - √5) / 2 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ 2 - √5 →
      Complex.normSq (A + (c₂ : ℂ) * B) ≤ Complex.normSq (A + (c₁ : ℂ) * B) := by
    intro c₁ c₂ hc1_lo hc12 hc2_hi
    rw [h_normSq_expand c₁, h_normSq_expand c₂, h_coeff_a, h_coeff_b, h_normSq_A]

    have h_sum_bound : c₁ + c₂ ≤ 2 * (2 - √5) := by linarith

    have h_factor_neg_at_bound : 2 * ((3*√5 - 10) / 2) + 2 * (2 - √5) * ((5 - √5) / 2) ≤ 0 := by
      have h0 : 2 * ((3*√5 - 10) / 2) = 3*√5 - 10 := by ring
      have h1 : 2 * (2 - √5) * ((5 - √5) / 2) = (2 - √5) * (5 - √5) := by ring
      have h2 : (2 - √5) * (5 - √5) = 15 - 7*√5 := by nlinarith [sqrt5_sq]
      rw [h0, h1, h2]

      nlinarith [sqrt5_sq]
    have h_factor_neg : 2 * (A * starRingEnd ℂ B).re + (c₁ + c₂) * Complex.normSq B ≤ 0 := by
      rw [h_coeff_b, h_coeff_a]
      calc 2 * ((3*√5 - 10) / 2) + (c₁ + c₂) * ((5 - √5) / 2)
          ≤ 2 * ((3*√5 - 10) / 2) + (2 * (2 - √5)) * ((5 - √5) / 2) := by
            have h_pos : (5 - √5) / 2 > 0 := h_a_pos
            have h_ineq : (c₁ + c₂) * ((5 - √5) / 2) ≤ (2 * (2 - √5)) * ((5 - √5) / 2) := by
              apply mul_le_mul_of_nonneg_right h_sum_bound (le_of_lt h_pos)
            linarith
        _ ≤ 0 := h_factor_neg_at_bound
    have h_diff : (11 - 4*√5) + 2 * c₂ * ((3*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2) -
                  ((11 - 4*√5) + 2 * c₁ * ((3*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2)) =
                  (c₂ - c₁) * ((3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
    have h_c_diff_nonneg : c₂ - c₁ ≥ 0 := by linarith
    have h_factor_neg' : (3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
      have h := h_factor_neg
      rw [h_coeff_b, h_coeff_a] at h
      linarith
    have h_prod_nonpos : (c₂ - c₁) * ((3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h_c_diff_nonneg h_factor_neg'
    linarith [h_diff, h_prod_nonpos]

  rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]
  calc Complex.normSq ((2 + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1))
      ≤ Complex.normSq ((2 + ζ₅^3 - 2*ζ₅^4) + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1)) := by
        apply h_mono ((1 - √5)/2) c (le_refl _) hc_lo hc_hi
    _ ≤ 3 + φ := by rw [← hA_def, ← hB_def, Complex.normSq_eq_norm_sq]; exact h_at_lower

lemma cross_disk_w2_z3_bound (c : ℝ) (hc_lo : (1 - √5) / 2 ≤ c) (hc_hi : c ≤ 2 - √5) :
    ‖((-2 : ℂ) + 2*ζ₅^4 - 2*ζ₅^3 + ζ₅^2) + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by

  set A : ℂ := -2 + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^3 - ζ₅^4 with hB_def

  have h_expr_eq : ∀ t : ℝ, ((-2 : ℂ) + 2*ζ₅^4 - 2*ζ₅^3 + ζ₅^2) + (t : ℂ) * (ζ₅^3 - ζ₅^4) =
      A + (t : ℂ) * B := by intro t; simp only [hA_def, hB_def]; ring

  rw [h_expr_eq, show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos), ← Complex.normSq_eq_norm_sq]

  have h_at_upper : Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) ≤ 3 + φ := by

    have h_w3 := w3_z3_at_lower_expr

    have h_match : A + ((2 - √5 : ℝ) : ℂ) * B = (-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4 := by
      simp only [hA_def, hB_def]; push_cast; ring
    rw [h_match]
    exact normSq_w3_z3_at_lower

  have h_coeff_a : Complex.normSq B = (5 - √5) / 2 := by rw [hB_def]; exact normSq_B
  have h_coeff_b : (A * starRingEnd ℂ B).re = (5*√5 - 10) / 2 := by
    rw [hA_def, hB_def]; exact re_A_w3_z3_mul_conj_B

  have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]

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
    rw [h_re_scale]; ring

  have h_normSq_A : Complex.normSq A = 16 - 7*√5 := by rw [hA_def]; exact normSq_A_w3_z3

  have h_endpoints_equal : Complex.normSq (A + (((1 - √5)/2 : ℝ) : ℂ) * B) =
      Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) := by
    rw [h_normSq_expand ((1-√5)/2), h_normSq_expand (2-√5), h_coeff_a, h_coeff_b, h_normSq_A]

    have h_c_lo_sq : ((1 - √5) / 2)^2 = (3 - √5) / 2 := by nlinarith [sqrt5_sq]
    have h_c_hi_sq : (2 - √5)^2 = 9 - 4*√5 := by nlinarith [sqrt5_sq]
    rw [h_c_lo_sq, h_c_hi_sq]
    ring_nf
    nlinarith [sqrt5_sq]

  have h_bound : ∀ c' : ℝ, (1 - √5) / 2 ≤ c' → c' ≤ 2 - √5 →
      Complex.normSq (A + (c' : ℂ) * B) ≤ Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) := by
    intro c' hc'_lo hc'_hi
    rw [h_normSq_expand c', h_normSq_expand (2-√5), h_coeff_a, h_coeff_b, h_normSq_A]

    have h_c_hi_sq : (2 - √5)^2 = 9 - 4*√5 := by nlinarith [sqrt5_sq]
    rw [h_c_hi_sq]

    have h_sqrt5_cubed : √5^3 = 5 * √5 := by
      have h1 : √5^3 = √5^2 * √5 := by ring
      rw [h1, sqrt5_sq]
    have h_diff_formula : (16 - 7*√5) + 2 * c' * ((5*√5 - 10) / 2) + c'^2 * ((5 - √5) / 2) -
        ((16 - 7*√5) + 2 * (2 - √5) * ((5*√5 - 10) / 2) + (9 - 4*√5) * ((5 - √5) / 2)) =
        (c' - (2 - √5)) * ((5*√5 - 10) + (c' + 2 - √5) * ((5 - √5) / 2)) := by
      ring_nf
      nlinarith [sqrt5_sq, h_sqrt5_cubed]

    have h_first_factor : c' - (2 - √5) ≤ 0 := by linarith

    have h_second_factor : (5*√5 - 10) + (c' + 2 - √5) * ((5 - √5) / 2) ≥ 0 := by
      have h_sum_lo : c' + 2 - √5 ≥ (1 - √5)/2 + 2 - √5 := by linarith
      have h_sum_simplified : (1 - √5)/2 + 2 - √5 = (5 - 3*√5) / 2 := by ring
      have h_at_lo : (5*√5 - 10) + ((5 - 3*√5) / 2) * ((5 - √5) / 2) = 0 := by nlinarith [sqrt5_sq]
      calc (5*√5 - 10) + (c' + 2 - √5) * ((5 - √5) / 2)
          ≥ (5*√5 - 10) + ((5 - 3*√5) / 2) * ((5 - √5) / 2) := by
            have h_pos : (5 - √5) / 2 > 0 := h_a_pos
            have h_ineq : (c' + 2 - √5) * ((5 - √5) / 2) ≥ ((5 - 3*√5) / 2) * ((5 - √5) / 2) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt h_pos)
              linarith [h_sum_lo, h_sum_simplified]
            linarith
        _ = 0 := h_at_lo
    have h_prod : (c' - (2 - √5)) * ((5*√5 - 10) + (c' + 2 - √5) * ((5 - √5) / 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h_first_factor h_second_factor
    linarith [h_diff_formula, h_prod]

  calc Complex.normSq (A + (c : ℂ) * B)
      ≤ Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) := h_bound c hc_lo hc_hi
    _ ≤ 3 + φ := h_at_upper

end TDCSG.CompoundSymmetry.GG5
