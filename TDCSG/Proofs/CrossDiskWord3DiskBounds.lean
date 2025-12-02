import TDCSG.Proofs.CrossDiskWord3Helpers

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions

set_option maxHeartbeats 2000000 in
lemma cross_disk_w3_z1_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖(ζ₅^4 - 2 : ℂ) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  set A : ℂ := ζ₅^4 - 2 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_one : ‖A + (1 : ℂ) * B‖^2 = 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    have h_expr : (ζ₅^4 - 2 : ℂ) + (1 : ℂ) * (1 - ζ₅) = ζ₅^4 - ζ₅ - 1 := by ring
    rw [h_expr]
    exact normSq_w3_z1_at_one

  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    have h_expr : (ζ₅^4 - 2 : ℂ) + ((2 - √5 : ℝ) : ℂ) * (1 - ζ₅) = ζ₅^4 - (2 - √5)*ζ₅ - √5 := by
      push_cast; ring
    rw [h_expr]
    exact normSq_w3_z1_at_lower

  have h_re_AB := re_A_w3_z1_mul_conj_B
  have h_normSq_B := normSq_B4
  have h_normSq_A := normSq_A_w3_z1
  have h_vertex := w3_z1_vertex
  have h_vertex_in := w3_z1_vertex_in_interval

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

  have h_normSq_B_pos : 0 < Complex.normSq B := by
    rw [hB_def, h_normSq_B]
    have h_sqrt5_lt5 : √5 < 5 := by nlinarith [sqrt5_sq]
    linarith

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (1 - ζ₅) = (5 - √5) / 2 := normSq_B4
  have h_coeff_b : ((ζ₅^4 - 2 : ℂ) * starRingEnd ℂ (1 - ζ₅)).re = (2*√5 - 5) / 2 := re_A_w3_z1_mul_conj_B
  have h_coeff_c : Complex.normSq (ζ₅^4 - 2) = 6 - √5 := normSq_A_w3_z1

  have h_f_le_max : Complex.normSq ((ζ₅^4 - 2) + (c : ℂ) * (1 - ζ₅)) ≤ 3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = ζ₅^4 - 2 by rfl, show B = 1 - ζ₅ by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    have h_f_at_1 : 6 - √5 + 2 * 1 * ((2*√5 - 5) / 2) + 1^2 * ((5 - √5) / 2) = 3 + φ := by
      simp only [φ, Real.goldenRatio]
      nlinarith [sqrt5_sq]

    have h_diff : (6 - √5 + 2 * c * ((2*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)) -
                  (6 - √5 + 2 * 1 * ((2*√5 - 5) / 2) + 1^2 * ((5 - √5) / 2)) =
                  (c - 1) * ((2*√5 - 5) + (c + 1) * ((5 - √5) / 2)) := by ring

    have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]

    have h_at_lower' : 6 - √5 + 2 * (2 - √5) * ((2*√5 - 5) / 2) + (2 - √5)^2 * ((5 - √5) / 2) ≤ 3 + φ := by
      have h_eq : 6 - √5 + 2 * (2 - √5) * ((2*√5 - 5) / 2) + (2 - √5)^2 * ((5 - √5) / 2) =
                  Complex.normSq (ζ₅^4 - (2 - √5)*ζ₅ - √5) := by
        rw [Complex.normSq_apply, w3_z1_at_lower_re, w3_z1_at_lower_im]
        simp only [← sq]
        have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
        nlinarith [sqrt5_sq, Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [Real.pi_pos] : 0 ≤ 2 * π / 5)
          (by linarith [Real.pi_pos] : 2 * π / 5 ≤ π), h_sin_sq]
      rw [h_eq]
      exact normSq_w3_z1_at_lower

    by_cases hc_lt_vertex : c < (3 - √5) / 4
    · have h_deriv_neg : c * ((5 - √5) / 2) * 2 + 2 * ((2*√5 - 5) / 2) < 0 := by
        have h1 : c * ((5 - √5) / 2) * 2 + 2 * ((2*√5 - 5) / 2) = c * (5 - √5) + (2*√5 - 5) := by ring
        rw [h1]
        have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [sqrt5_sq]
        have h_vertex_eq : (5 - 2*√5) / (5 - √5) = (3 - √5) / 4 := by grind
        have h_ineq : c * (5 - √5) < 5 - 2*√5 := by
          calc c * (5 - √5) < (3 - √5) / 4 * (5 - √5) := by
                apply mul_lt_mul_of_pos_right hc_lt_vertex h_5_minus_sqrt5_pos
            _ = (5 - 2*√5) := by nlinarith [sqrt5_sq]
        linarith

      have h_mono : ∀ c₁ c₂ : ℝ, 2 - √5 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ (3 - √5) / 4 →
          6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2) ≤
          6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2) := by
        intro c₁ c₂ _ hc12 hc2v
        have h_diff2 : (6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2)) -
                      (6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2)) =
                      (c₂ - c₁) * ((2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
        have h_sum_bound : c₁ + c₂ ≤ 2 * (3 - √5) / 4 := by linarith
        have h_factor_neg : (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
          have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [sqrt5_sq]
          have h_at_2v : (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) = 0 := by
            nlinarith [sqrt5_sq]
          calc (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)
              ≤ (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) := by gcongr
            _ = 0 := h_at_2v
        nlinarith [hc12, h_factor_neg]

      calc 6 - √5 + 2 * c * ((2*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)
          ≤ 6 - √5 + 2 * (2 - √5) * ((2*√5 - 5) / 2) + (2 - √5)^2 * ((5 - √5) / 2) := by
            apply h_mono (2 - √5) c (le_refl _) hc_lo (le_of_lt hc_lt_vertex)
        _ ≤ 3 + φ := h_at_lower'

    · push_neg at hc_lt_vertex

      have h_mono : ∀ c₁ c₂ : ℝ, (3 - √5) / 4 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ 1 →
          6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2) ≤
          6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2) := by
        intro c₁ c₂ hc1v hc12 _
        have h_diff2 : (6 - √5 + 2 * c₂ * ((2*√5 - 5) / 2) + c₂^2 * ((5 - √5) / 2)) -
                      (6 - √5 + 2 * c₁ * ((2*√5 - 5) / 2) + c₁^2 * ((5 - √5) / 2)) =
                      (c₂ - c₁) * ((2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring
        have h_sum_bound : c₁ + c₂ ≥ 2 * (3 - √5) / 4 := by linarith
        have h_factor_pos : (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2) ≥ 0 := by
          have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [sqrt5_sq]
          have h_at_2v : (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) = 0 := by
            nlinarith [sqrt5_sq]
          calc (2*√5 - 5) + (c₁ + c₂) * ((5 - √5) / 2)
              ≥ (2*√5 - 5) + (2 * (3 - √5) / 4) * ((5 - √5) / 2) := by gcongr
            _ = 0 := h_at_2v
        nlinarith [hc12, h_factor_pos]

      calc 6 - √5 + 2 * c * ((2*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)
          ≤ 6 - √5 + 2 * 1 * ((2*√5 - 5) / 2) + 1^2 * ((5 - √5) / 2) := by
            apply h_mono c 1 hc_lt_vertex hc_hi (le_refl 1)
        _ = 3 + φ := h_f_at_1

  exact h_f_le_max

set_option maxHeartbeats 1600000 in

lemma cross_disk_w3_z2_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  set A : ℂ := (2 : ℂ) + ζ₅^3 - 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_one : ‖A + (1 : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z2_at_one_expr]
    exact normSq_w3_z2_at_one

  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z2_at_lower_expr]
    exact normSq_w3_z2_at_lower

  have h_normSq_B := normSq_B3
  have h_normSq_A := normSq_A_w3_z2
  have h_re_AB := re_A_w3_z2_mul_conj_B
  have h_vertex := w3_z2_vertex_above_interval

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

  have h_normSq_B_pos : 0 < Complex.normSq B := by
    rw [hB_def, h_normSq_B]
    have h_sqrt5_lt5 : √5 < 5 := by nlinarith [sqrt5_sq]
    linarith

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (ζ₅^4 - 1) = (5 - √5) / 2 := normSq_B3
  have h_coeff_b : (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re = (3*√5 - 10) / 2 := re_A_w3_z2_mul_conj_B
  have h_coeff_c : Complex.normSq ((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) = 11 - 4*√5 := normSq_A_w3_z2

  have h_f_le_max : Complex.normSq (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)) ≤ 3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = (2 : ℂ) + ζ₅^3 - 2*ζ₅^4 by rfl, show B = ζ₅^4 - 1 by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    have h_f_mono : ∀ c₁ c₂ : ℝ, c₁ ≤ c₂ → c₂ ≤ 1 →
        11 - 4*√5 + 2 * c₂ * ((3*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2) ≤
        11 - 4*√5 + 2 * c₁ * ((3*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2) := by
      intro c₁ c₂ hc12 hc2_le1
      have h_diff : (11 - 4*√5 + 2 * c₂ * ((3*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2)) -
                    (11 - 4*√5 + 2 * c₁ * ((3*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2)) =
                    (c₂ - c₁) * ((3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring

      have h_sum_bound : c₁ + c₂ ≤ 2 := by linarith
      have h_factor_neg : (3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
        have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [sqrt5_sq]

        calc (3*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)
            ≤ (3*√5 - 10) + 2 * ((5 - √5) / 2) := by gcongr
          _ = 2*√5 - 5 := by ring
          _ ≤ 0 := by nlinarith [sqrt5_sq]
      nlinarith [hc12, h_factor_neg]

    calc 11 - 4*√5 + 2 * c * ((3*√5 - 10) / 2) + c^2 * ((5 - √5) / 2)
        ≤ 11 - 4*√5 + 2 * (2 - √5) * ((3*√5 - 10) / 2) + (2 - √5)^2 * ((5 - √5) / 2) := by
          apply h_f_mono (2 - √5) c (by linarith [hc_lo]) hc_hi
      _ ≤ 3 + φ := by
          have h_eq : 11 - 4*√5 + 2 * (2 - √5) * ((3*√5 - 10) / 2) + (2 - √5)^2 * ((5 - √5) / 2) =
                      Complex.normSq ((√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4) := by
            rw [Complex.normSq_apply, w3_z2_at_lower_re, w3_z2_at_lower_im]
            simp only [← sq]
            have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
              rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
              rw [Real.cos_pi_div_five]
              ring
            have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
            have h_im_simp : √5 * Real.sin (2 * π / 5) - Real.sin (π / 5) =
                Real.sin (π / 5) * (√5 + 3) / 2 := by
              rw [h_sin_double]

              have h_sqrt5_prod : √5 * (1 + √5) = √5 + 5 := by nlinarith [sqrt5_sq]
              calc √5 * (Real.sin (π / 5) * (1 + √5) / 2) - Real.sin (π / 5)
                  = Real.sin (π / 5) * (√5 * (1 + √5) / 2 - 1) := by ring
                _ = Real.sin (π / 5) * ((√5 + 5) / 2 - 1) := by rw [h_sqrt5_prod]
                _ = Real.sin (π / 5) * (√5 + 3) / 2 := by ring
            rw [h_im_simp]
            have h_im_sq : (Real.sin (π / 5) * (√5 + 3) / 2)^2 =
                Real.sin (π / 5)^2 * (√5 + 3)^2 / 4 := by ring
            have h_sqrt5_plus_3_sq : (√5 + 3)^2 = 14 + 6*√5 := by nlinarith [sqrt5_sq]
            rw [h_im_sq, h_sin_sq, h_sqrt5_plus_3_sq]
            nlinarith [sqrt5_sq]
          rw [h_eq]
          exact normSq_w3_z2_at_lower

  exact h_f_le_max

set_option maxHeartbeats 1600000 in

lemma cross_disk_w3_z3_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by
  set A : ℂ := ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) with hA_def
  set B : ℂ := ζ₅^3 - ζ₅^4 with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_one : ‖A + (1 : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z3_at_one_expr]
    exact normSq_w3_z3_at_one

  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z3_at_lower_expr]
    exact normSq_w3_z3_at_lower

  have h_normSq_B := normSq_B
  have h_normSq_A := normSq_A_w3_z3
  have h_re_AB := re_A_w3_z3_mul_conj_B
  have h_vertex := w3_z3_vertex_below_interval

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

  have h_normSq_B_pos : 0 < Complex.normSq B := by
    rw [hB_def, h_normSq_B]
    have h_sqrt5_lt5 : √5 < 5 := by nlinarith [sqrt5_sq]
    linarith

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (ζ₅^3 - ζ₅^4) = (5 - √5) / 2 := normSq_B
  have h_coeff_b : (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re =
      (5*√5 - 10) / 2 := re_A_w3_z3_mul_conj_B
  have h_coeff_c : Complex.normSq ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) = 16 - 7*√5 := normSq_A_w3_z3

  have h_f_le_max : Complex.normSq (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (c : ℂ) * (ζ₅^3 - ζ₅^4)) ≤
      3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = ((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) by rfl, show B = ζ₅^3 - ζ₅^4 by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    have h_f_mono : ∀ c₁ c₂ : ℝ, 2 - √5 ≤ c₁ → c₁ ≤ c₂ →
        16 - 7*√5 + 2 * c₁ * ((5*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2) ≤
        16 - 7*√5 + 2 * c₂ * ((5*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2) := by
      intro c₁ c₂ hc1_lo hc12
      have h_diff : (16 - 7*√5 + 2 * c₂ * ((5*√5 - 10) / 2) + c₂^2 * ((5 - √5) / 2)) -
                    (16 - 7*√5 + 2 * c₁ * ((5*√5 - 10) / 2) + c₁^2 * ((5 - √5) / 2)) =
                    (c₂ - c₁) * ((5*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring

      have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [sqrt5_sq]
      have h_sum_ge : c₁ + c₂ ≥ 2 * (2 - √5) := by linarith
      have h_factor_nonneg : (5*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2) ≥ 0 := by

        calc (5*√5 - 10) + (c₁ + c₂) * ((5 - √5) / 2)
            ≥ (5*√5 - 10) + 2 * (2 - √5) * ((5 - √5) / 2) := by gcongr
          _ = (5*√5 - 10) + (2 - √5) * (5 - √5) := by ring
          _ = 5 - 2*√5 := by nlinarith [sqrt5_sq]
          _ ≥ 0 := by nlinarith [sqrt5_sq]
      nlinarith [hc12, h_factor_nonneg]

    have h_f_at_1_le : 16 - 7*√5 + 2 * 1 * ((5*√5 - 10) / 2) + 1^2 * ((5 - √5) / 2) ≤ 3 + φ := by
      simp only [φ, Real.goldenRatio]
      nlinarith [sqrt5_sq, Real.goldenRatio_pos]

    calc 16 - 7*√5 + 2 * c * ((5*√5 - 10) / 2) + c^2 * ((5 - √5) / 2)
        ≤ 16 - 7*√5 + 2 * 1 * ((5*√5 - 10) / 2) + 1^2 * ((5 - √5) / 2) := by
          apply h_f_mono c 1 hc_lo hc_hi
      _ ≤ 3 + φ := h_f_at_1_le

  exact h_f_le_max

lemma cross_disk_w3_z4_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  set A : ℂ := (4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_normSq_B := normSq_B3
  have h_normSq_A := normSq_A_w3_z4
  have h_re_AB := re_A_w3_z4_mul_conj_B

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

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (ζ₅^4 - 1) = (5 - √5) / 2 := normSq_B3
  have h_coeff_b : (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) * starRingEnd ℂ (ζ₅^4 - 1)).re =
      (6*√5 - 15) / 2 := re_A_w3_z4_mul_conj_B
  have h_coeff_c : Complex.normSq ((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) = 31 - 12*√5 := normSq_A_w3_z4

  have h_f_le_max : Complex.normSq (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)) ≤
      3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = (4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4 by rfl, show B = ζ₅^4 - 1 by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    simp only [φ, Real.goldenRatio]
    nlinarith [sqrt5_sq, hc_lo, hc_hi, sq_nonneg c, sq_nonneg (c - 1),
               sq_nonneg (c - (2 - √5)), Real.sqrt_nonneg 5]

  exact h_f_le_max

set_option maxHeartbeats 1600000 in

lemma cross_disk_w3_z5_bound (c : ℝ) (hc_lo : 2 - √5 ≤ c) (hc_hi : c ≤ 1) :
    ‖((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  set A : ℂ := (-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by simp only [φ]; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_one : ‖A + (1 : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    have h_expr : ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (1 : ℂ) * (1 - ζ₅) = -3 + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4 := by ring
    rw [h_expr]
    exact normSq_w3_z5_at_one

  have h_at_lower : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [w3_z5_at_lower_expr]
    exact normSq_w3_z5_at_lower

  have h_normSq_B := normSq_B4
  have h_normSq_A := normSq_A_w3_z5
  have h_re_AB := re_A_w3_z5_mul_conj_B
  have h_vertex := w3_z5_vertex_above_interval

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

  have h_normSq_B_pos : 0 < Complex.normSq B := by
    rw [hB_def, h_normSq_B]
    have h_sqrt5_lt5 : √5 < 5 := by nlinarith [sqrt5_sq]
    linarith

  rw [hA_def, hB_def]
  rw [← Complex.normSq_eq_norm_sq]

  have h_coeff_a : Complex.normSq (1 - ζ₅) = (5 - √5) / 2 := normSq_B4
  have h_coeff_b : (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re = (7*√5 - 20) / 2 := re_A_w3_z5_mul_conj_B
  have h_coeff_c : Complex.normSq ((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) = 46 - 19*√5 := normSq_A_w3_z5

  have h_f_le_max : Complex.normSq (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (c : ℂ) * (1 - ζ₅)) ≤ 3 + φ := by
    rw [h_normSq_expand c]
    rw [show A = (-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4 by rfl, show B = 1 - ζ₅ by rfl]
    rw [h_coeff_c, h_coeff_b, h_coeff_a]

    have h_f_mono : ∀ c₁ c₂ : ℝ, c₁ ≤ c₂ → c₂ ≤ 1 →
        46 - 19*√5 + 2 * c₂ * ((7*√5 - 20) / 2) + c₂^2 * ((5 - √5) / 2) ≤
        46 - 19*√5 + 2 * c₁ * ((7*√5 - 20) / 2) + c₁^2 * ((5 - √5) / 2) := by
      intro c₁ c₂ hc12 hc2_le1
      have h_diff : (46 - 19*√5 + 2 * c₂ * ((7*√5 - 20) / 2) + c₂^2 * ((5 - √5) / 2)) -
                    (46 - 19*√5 + 2 * c₁ * ((7*√5 - 20) / 2) + c₁^2 * ((5 - √5) / 2)) =
                    (c₂ - c₁) * ((7*√5 - 20) + (c₁ + c₂) * ((5 - √5) / 2)) := by ring

      have h_sum_bound : c₁ + c₂ ≤ 2 := by linarith
      have h_factor_neg : (7*√5 - 20) + (c₁ + c₂) * ((5 - √5) / 2) ≤ 0 := by
        have h_5_minus_sqrt5_pos : 5 - √5 > 0 := by nlinarith [sqrt5_sq]

        calc (7*√5 - 20) + (c₁ + c₂) * ((5 - √5) / 2)
            ≤ (7*√5 - 20) + 2 * ((5 - √5) / 2) := by gcongr
          _ = 6*√5 - 15 := by ring
          _ ≤ 0 := by nlinarith [sqrt5_sq]
      nlinarith [hc12, h_factor_neg]

    calc 46 - 19*√5 + 2 * c * ((7*√5 - 20) / 2) + c^2 * ((5 - √5) / 2)
        ≤ 46 - 19*√5 + 2 * (2 - √5) * ((7*√5 - 20) / 2) + (2 - √5)^2 * ((5 - √5) / 2) := by
          apply h_f_mono (2 - √5) c (by linarith [hc_lo]) hc_hi
      _ ≤ 3 + φ := by
          have h_eq : 46 - 19*√5 + 2 * (2 - √5) * ((7*√5 - 20) / 2) + (2 - √5)^2 * ((5 - √5) / 2) =
                      Complex.normSq ((-2 - √5 : ℂ) + (2 + √5 : ℂ) * ζ₅ - 2*ζ₅^2 + ζ₅^4) := by
            rw [Complex.normSq_apply, w3_z5_at_lower_re, w3_z5_at_lower_im]
            simp only [← sq]
            have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
            have h_im_sq : (Real.sin (π / 5) * (1 + √5))^2 = Real.sin (π / 5)^2 * (1 + √5)^2 := by ring
            have h_1_plus_sqrt5_sq : (1 + √5)^2 = 6 + 2*√5 := by nlinarith [sqrt5_sq]
            rw [h_im_sq, h_sin_sq, h_1_plus_sqrt5_sq]
            nlinarith [sqrt5_sq]
          rw [h_eq]
          exact normSq_w3_z5_at_lower

  exact h_f_le_max

end TDCSG.CompoundSymmetry.GG5
