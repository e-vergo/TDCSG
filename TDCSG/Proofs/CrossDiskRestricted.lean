import TDCSG.Proofs.CrossDiskBasic

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions (segment_length translation_length_1 translation_length_2 segmentPoint psi t_F E E' F G ζ₅ zeta5 zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

lemma cross_disk_z2_bound_restricted (c : ℝ) (hc_lo : -1 ≤ c) (hc_hi : c ≤ (1 - √5) / 2) :
    ‖(-2 : ℂ) + ζ₅^2 + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by
  set A : ℂ := -2 + ζ₅^2 with hA_def
  set B : ℂ := ζ₅^3 - ζ₅^4 with hB_def

  have hB_ne : B ≠ 0 := by rw [hB_def]; exact zeta5_cubed_minus_fourth_ne_zero

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := three_plus_phi_pos
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_neg1 : ‖A + ((-1 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    have h_neg1 : ((-1 : ℝ) : ℂ) * B = -B := by simp
    rw [h_neg1]
    have h_expr : A + -B = -2 + ζ₅^2 - ζ₅^3 + ζ₅^4 := by rw [hA_def, hB_def]; ring
    rw [h_expr]
    exact normSq_at_neg1

  have h_coerce : (((1 - √5)/2 : ℝ) : ℂ) = (1 - (√5 : ℂ)) / 2 := by
    push_cast
    ring

  have h_f_at_upper_eq : ‖A + (((1 - √5)/2) : ℂ) * B‖^2 = 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    convert normSq_at_upper_endpoint using 2
    rw [h_coerce]

  have h_mono : ‖A + (c : ℂ) * B‖^2 ≤ ‖A + (((1 - √5)/2) : ℂ) * B‖^2 := by
    rw [hA_def, hB_def]
    simp only [← Complex.normSq_eq_norm_sq]
    have h_upper_bound : (1 - √5) / 2 ≥ c := hc_hi
    have h_lower_bound : c ≥ -1 := hc_lo
    have h_convex_max : Complex.normSq (-2 + ζ₅^2 + (c : ℂ) * (ζ₅^3 - ζ₅^4)) ≤
                        Complex.normSq (-2 + ζ₅^2 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^3 - ζ₅^4)) := by

      let c_upper : ℝ := (1 - √5) / 2

      have h_re_AB : (((-2 : ℂ) + ζ₅^2) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re = 3 * √5 / 2 :=
        re_A_mul_conj_B
      have h_normSq_B : Complex.normSq (ζ₅^3 - ζ₅^4) = (5 - √5) / 2 := normSq_B
      have h_vertex : -(3 * √5 / 2) / ((5 - √5) / 2) < -1 := vertex_lt_neg1

      have h_normSq_B_pos : 0 < Complex.normSq (ζ₅^3 - ζ₅^4) := by
        rw [h_normSq_B]
        have h_sqrt5_lt5 : √5 < 5 := by
          have : √5 < √25 := Real.sqrt_lt_sqrt (by linarith) (by norm_num)
          have h25 : √25 = 5 := by
            rw [show (25 : ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
          linarith
        linarith

      have h_c_le_upper : c ≤ c_upper := hc_hi
      have h_diff_nonneg : c_upper - c ≥ 0 := by linarith

      have h_vertex_lt_c : -(3 * √5 / 2) / ((5 - √5) / 2) < c := by grind

      have h_sum_gt_2vertex : c + c_upper > 2 * (-(3 * √5 / 2) / ((5 - √5) / 2)) := by
        grind

      have h_factor_pos : 2 * (3 * √5 / 2) + (c + c_upper) * ((5 - √5) / 2) > 0 := by
        have h_5_minus_sqrt5_pos : 0 < 5 - √5 := by
          have h_sqrt5_lt5 : √5 < 5 := by
            have : √5 < √25 := Real.sqrt_lt_sqrt (by linarith) (by norm_num)
            have h25 : √25 = 5 := by
              rw [show (25 : ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
            linarith
          linarith
        have h_denom_pos : 0 < (5 - √5) / 2 := by linarith
        have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
        have h2v : 2 * (-(3 * √5 / 2) / ((5 - √5) / 2)) = -6 * √5 / (5 - √5) := by
          field_simp
          ring
        rw [h2v] at h_sum_gt_2vertex
        have h_prod : (c + c_upper) * ((5 - √5) / 2) > -3 * √5 := by
          have h1 : -6 * √5 / (5 - √5) * ((5 - √5) / 2) = -3 * √5 := by
            field_simp
            ring
          calc (c + c_upper) * ((5 - √5) / 2) > -6 * √5 / (5 - √5) * ((5 - √5) / 2) := by
                apply mul_lt_mul_of_pos_right h_sum_gt_2vertex h_denom_pos
            _ = -3 * √5 := h1
        linarith

      have h_normSq_expand : ∀ t : ℝ, Complex.normSq ((-2 : ℂ) + ζ₅^2 + (t : ℂ) * (ζ₅^3 - ζ₅^4)) =
          Complex.normSq ((-2 : ℂ) + ζ₅^2) +
          2 * t * (((-2 : ℂ) + ζ₅^2) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re +
          t^2 * Complex.normSq (ζ₅^3 - ζ₅^4) := by
        intro t
        rw [Complex.normSq_add]
        have h_conj_t : starRingEnd ℂ (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
        have h_normSq_t : Complex.normSq (t : ℂ) = t^2 := by
          rw [Complex.normSq_ofReal]; ring
        rw [Complex.normSq_mul, h_normSq_t]
        simp only [map_mul, h_conj_t]
        have h_re_scale : ((-2 + ζ₅^2) * ((t : ℂ) * starRingEnd ℂ (ζ₅^3 - ζ₅^4))).re =
            t * (((-2 : ℂ) + ζ₅^2) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)).re := by
          have h_assoc : (-2 + ζ₅^2) * ((t : ℂ) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)) =
              (t : ℂ) * ((-2 + ζ₅^2) * starRingEnd ℂ (ζ₅^3 - ζ₅^4)) := by ring
          rw [h_assoc, Complex.re_ofReal_mul]
        rw [h_re_scale]
        ring

      rw [h_normSq_expand c, h_normSq_expand c_upper]
      rw [h_re_AB, h_normSq_B]
      have h_diff : Complex.normSq ((-2 : ℂ) + ζ₅^2) + 2 * c_upper * (3 * √5 / 2) +
          c_upper ^ 2 * ((5 - √5) / 2) -
          (Complex.normSq ((-2 : ℂ) + ζ₅^2) + 2 * c * (3 * √5 / 2) + c ^ 2 * ((5 - √5) / 2)) =
          (c_upper - c) * (2 * (3 * √5 / 2) + (c + c_upper) * ((5 - √5) / 2)) := by ring
      nlinarith [h_factor_pos, h_diff_nonneg, h_diff]

    convert h_convex_max using 2
    rw [h_coerce]
  grind

lemma B3_re : (ζ₅^4 - 1 : ℂ).re = (√5 - 5) / 4 := by
  simp only [Complex.sub_re, Complex.one_re]
  rw [zeta5_pow4_re]
  ring

lemma B3_im : (ζ₅^4 - 1 : ℂ).im = -Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im, Complex.one_im]
  rw [zeta5_pow4_im_neg, zeta5_im_eq_sin]
  ring

lemma normSq_B3 : Complex.normSq (ζ₅^4 - 1) = (5 - √5) / 2 := by
  rw [Complex.normSq_apply]
  simp only [← sq]
  rw [B3_re, B3_im]
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := by
    have h_cos : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
      rw [cos_two_pi_fifth]
      unfold Real.goldenRatio
      ring
    have h := Real.sin_sq_add_cos_sq (2 * π / 5)
    have h1 : Real.sin (2 * π / 5)^2 = 1 - Real.cos (2 * π / 5)^2 := by linarith
    grind
  grind

lemma sin_sq_two_pi_div_5 : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := by
  have h_cos : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
    rw [cos_two_pi_fifth]
    unfold Real.goldenRatio
    ring
  have h := Real.sin_sq_add_cos_sq (2 * π / 5)
  have h1 : Real.sin (2 * π / 5)^2 = 1 - Real.cos (2 * π / 5)^2 := by linarith
  grind

lemma z3_normSq_at_c_upper :
    Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1)) = (7 + √5) / 2 := by
  rw [Complex.normSq_apply]
  simp only [← sq]

  have h_re : ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1)).re = 1 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               Complex.one_re, Complex.sub_im, Complex.one_im]
    have h2re : (2 : ℂ).re = 2 := by rfl
    have h2im : (2 : ℂ).im = 0 := by rfl
    rw [h2re, h2im]
    simp only [zero_mul, sub_zero]
    rw [zeta5_re, zeta5_cubed_re, zeta5_pow4_re]

    have h3 : (1 - √5) * (√5 - 5) = 6*√5 - 10 := by nlinarith [sqrt5_sq]
    nlinarith [sqrt5_sq, h3]

  have h_im : ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1)).im =
              -Real.sin (2 * π / 5) * (5 - √5) / 2 - Real.sin (π / 5) := by
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have h2im : (2 : ℂ).im = 0 := by rfl
    have h2re : (2 : ℂ).re = 2 := by rfl
    have h1im : (1 : ℂ).im = 0 := by rfl
    simp only [h2im, h2re, h1im, zero_mul, add_zero, zero_sub, sub_zero]
    rw [zeta5_im_eq_sin, zeta5_cubed_im_eq, zeta5_pow4_im_neg, zeta5_im_eq_sin]
    ring

  rw [h_re, h_im]

  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_pi5_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5

  have h_product : Real.sin (2 * π / 5) * (5 - √5) / 2 = Real.sin (π / 5) * √5 := by
    rw [h_sin_double]
    have h1 : (1 + √5) * (5 - √5) = 5 - √5 + 5*√5 - √5^2 := by ring
    have h2 : (1 + √5) * (5 - √5) = 4 * √5 := by nlinarith [sqrt5_sq, h1]
    have h3 : Real.sin (π / 5) * (1 + √5) * (5 - √5) = Real.sin (π / 5) * (4 * √5) := by
      grind
    grind

  have h_im_simp : -Real.sin (2 * π / 5) * (5 - √5) / 2 - Real.sin (π / 5) =
                   -Real.sin (π / 5) * (√5 + 1) := by
    have h := h_product
    linarith
  grind

lemma seven_plus_sqrt5_div_2_eq : (7 + √5) / 2 = 3 + φ := by
  unfold φ Real.goldenRatio
  ring

lemma cross_disk_z3_bound_restricted (c : ℝ) (hc_lo : -1 ≤ c) (hc_hi : c ≤ (1 - √5) / 2) :
    ‖(2 : ℂ) - 2*ζ₅ + ζ₅^3 + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  set A : ℂ := 2 - 2*ζ₅ + ζ₅^3 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  have hB_ne : B ≠ 0 := by
    rw [hB_def]
    intro h
    have : ζ₅^4 = 1 := sub_eq_zero.mp h
    have h1 : ζ₅^4 ≠ 1 := zeta5_pow_ne_one (by norm_num) (by norm_num)
    exact h1 this

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := three_plus_phi_pos
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_vertex_lt : (1 - 3*√5) / 4 < -1 := by
    have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)

    have h_sqrt5_gt : √5 > 5/3 := by
      have h_sq : (5/3 : ℝ)^2 = 25/9 := by norm_num
      have h_lt : (25/9 : ℝ) < 5 := by norm_num

      calc √5 > √(25/9) := Real.sqrt_lt_sqrt (by norm_num) h_lt
        _ = 5/3 := by rw [← h_sq, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5/3)]
    linarith

  have h_at_c_upper : ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 = 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [z3_normSq_at_c_upper, seven_plus_sqrt5_div_2_eq]

  have h_mono : ‖A + (c : ℂ) * B‖^2 ≤ ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 := by
    rw [hA_def, hB_def]
    simp only [← Complex.normSq_eq_norm_sq]

    have h_normSq_expand : ∀ t : ℝ, Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (t : ℂ) * (ζ₅^4 - 1)) =
        Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3) +
        2 * t * (((2 : ℂ) - 2*ζ₅ + ζ₅^3) * starRingEnd ℂ (ζ₅^4 - 1)).re +
        t^2 * Complex.normSq (ζ₅^4 - 1) := by
      intro t
      rw [Complex.normSq_add]
      have h_conj_t : starRingEnd ℂ (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      have h_normSq_t : Complex.normSq (t : ℂ) = t^2 := by
        rw [Complex.normSq_ofReal]; ring
      rw [Complex.normSq_mul, h_normSq_t]
      simp only [map_mul, h_conj_t]
      have h_re_scale : (((2 : ℂ) - 2*ζ₅ + ζ₅^3) * ((t : ℂ) * starRingEnd ℂ (ζ₅^4 - 1))).re =
          t * ((((2 : ℂ) - 2*ζ₅ + ζ₅^3) * starRingEnd ℂ (ζ₅^4 - 1)).re) := by
        have h_assoc : ((2 : ℂ) - 2*ζ₅ + ζ₅^3) * ((t : ℂ) * starRingEnd ℂ (ζ₅^4 - 1)) =
            (t : ℂ) * (((2 : ℂ) - 2*ζ₅ + ζ₅^3) * starRingEnd ℂ (ζ₅^4 - 1)) := by ring
        rw [h_assoc, Complex.re_ofReal_mul]
      rw [h_re_scale]
      ring

    have h_conj_B3 : starRingEnd ℂ (ζ₅^4 - 1) = ζ₅ - 1 := by
      rw [map_sub, map_one]
      have : starRingEnd ℂ (ζ₅^4) = ζ₅ := by
        rw [map_pow, zeta5_conj]
        calc (ζ₅^4)^4 = ζ₅^16 := by ring
          _ = ζ₅ := zeta5_pow_sixteen
      rw [this]

    have h_re_AB : (((2 : ℂ) - 2*ζ₅ + ζ₅^3) * starRingEnd ℂ (ζ₅^4 - 1)).re = (4*√5 - 5) / 2 := by
      rw [h_conj_B3]
      have h_expand : ((2 : ℂ) - 2*ζ₅ + ζ₅^3) * (ζ₅ - 1) = -2 + 4*ζ₅ - 2*ζ₅^2 - ζ₅^3 + ζ₅^4 := by ring
      rw [h_expand]
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
      have h2re : (2 : ℂ).re = 2 := by rfl
      have h2im : (2 : ℂ).im = 0 := by rfl
      have h4re : (4 : ℂ).re = 4 := by rfl
      have h4im : (4 : ℂ).im = 0 := by rfl
      simp only [h2re, h2im, h4re, h4im, zero_mul]
      rw [zeta5_re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
      ring

    have h_normSq_B : Complex.normSq (ζ₅^4 - 1) = (5 - √5) / 2 := normSq_B3

    rw [h_normSq_expand c, h_normSq_expand ((1 - √5) / 2)]
    rw [h_re_AB, h_normSq_B]

    let c_upper : ℝ := (1 - √5) / 2

    have h_5_minus_sqrt5_pos : 0 < 5 - √5 := by
      have h25 : √25 = 5 := by
        rw [show (25 : ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
      have : √5 < 5 := by
        calc √5 < √25 := Real.sqrt_lt_sqrt (by linarith) (by norm_num)
          _ = 5 := h25
      linarith

    have h_diff_expand : Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3) + 2 * c_upper * ((4*√5 - 5) / 2) +
        c_upper^2 * ((5 - √5) / 2) -
        (Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3) + 2 * c * ((4*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)) =
        (c_upper - c) * ((4*√5 - 5) + (c + c_upper) * ((5 - √5) / 2)) := by ring

    have h_c_upper_def : c_upper = (1 - √5) / 2 := rfl
    have h_c_plus_cupper_lo : c + c_upper ≥ -1 + (1 - √5) / 2 := by
      linarith [hc_lo]
    have h_lo_val : -1 + (1 - √5) / 2 = -(1 + √5) / 2 := by ring

    have h_factor_pos : (4*√5 - 5) + (c + c_upper) * ((5 - √5) / 2) ≥ 0 := by
      have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
      have h_sqrt5_gt : √5 > 5 / 3 := by
        have h_sq : (5/3 : ℝ)^2 = 25/9 := by norm_num
        have h_lt : (25/9 : ℝ) < 5 := by norm_num
        calc √5 > √(25/9) := Real.sqrt_lt_sqrt (by norm_num) h_lt
          _ = 5/3 := by rw [← h_sq, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5/3)]

      have h_at_min : (4*√5 - 5) + (-(1 + √5) / 2) * ((5 - √5) / 2) = 3*√5 - 5 := by
        nlinarith [sqrt5_sq]
      have h_3sqrt5_gt_5 : 3*√5 > 5 := by linarith [h_sqrt5_gt]

      have h_ge : (4*√5 - 5) + (c + c_upper) * ((5 - √5) / 2) ≥ 3*√5 - 5 := by
        have h1 : (5 - √5) / 2 > 0 := by linarith
        have h2 : c + c_upper ≥ -(1 + √5) / 2 := by rw [← h_lo_val]; exact h_c_plus_cupper_lo

        calc (4*√5 - 5) + (c + c_upper) * ((5 - √5) / 2)
            ≥ (4*√5 - 5) + (-(1 + √5) / 2) * ((5 - √5) / 2) := by nlinarith
          _ = 3*√5 - 5 := h_at_min
      linarith [h_ge, h_3sqrt5_gt_5]

    have h_cupper_minus_c : c_upper - c ≥ 0 := by
      rw [h_c_upper_def]
      linarith [hc_hi]

    nlinarith [h_factor_pos, h_cupper_minus_c, h_diff_expand, sqrt5_sq]
  grind

lemma B4_re : (1 - ζ₅ : ℂ).re = (5 - √5) / 4 := by
  simp only [Complex.sub_re, Complex.one_re]
  rw [zeta5_re]
  ring

lemma B4_im : (1 - ζ₅ : ℂ).im = -Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im, Complex.one_im]
  rw [zeta5_im_eq_sin]
  ring

lemma normSq_B4 : Complex.normSq (1 - ζ₅) = (5 - √5) / 2 := by
  rw [Complex.normSq_apply]
  simp only [← sq]
  rw [B4_re, B4_im]
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  grind

lemma A4_re : ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (-9 + 5*√5) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  ring

lemma A4_im : ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4).im = Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im]
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h2re, h2im]
  rw [zeta5_im_eq_sin, zeta5_sq_im', zeta5_pow4_im']
  ring

lemma conj_B4 : starRingEnd ℂ (1 - ζ₅) = 1 - ζ₅^4 := by
  rw [map_sub, map_one, zeta5_conj]

lemma re_A4_mul_conj_B4 :
    (((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re = (5*√5 - 10) / 2 := by
  rw [conj_B4]
  have h_expand : ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * (1 - ζ₅^4) =
      -2 + 2*ζ₅^4 + 2*ζ₅ - 2*ζ₅^5 - 2*ζ₅^2 + 2*ζ₅^6 + ζ₅^4 - ζ₅^8 := by ring
  rw [h_expand]
  have h_simp : (-2 : ℂ) + 2*ζ₅^4 + 2*ζ₅ - 2*ζ₅^5 - 2*ζ₅^2 + 2*ζ₅^6 + ζ₅^4 - ζ₅^8 =
      -4 + 3*ζ₅^4 + 4*ζ₅ - 2*ζ₅^2 - ζ₅^3 := by
    rw [zeta5_pow_five, zeta5_pow_six, zeta5_pow_eight]; ring
  rw [h_simp]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
  have h4re : (4 : ℂ).re = 4 := by rfl
  have h4im : (4 : ℂ).im = 0 := by rfl
  have h3re : (3 : ℂ).re = 3 := by rfl
  have h3im : (3 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h4re, h4im, h3re, h3im, h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_sq_re, zeta5_cubed_re, zeta5_pow4_re]
  ring

lemma A4_at_neg1_re : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (-7 + 3*√5) / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
  have h3re : (3 : ℂ).re = 3 := by rfl
  have h3im : (3 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h3re, h3im, h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  ring

lemma A4_at_neg1_im : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).im = 2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im]
  have h3re : (3 : ℂ).re = 3 := by rfl
  have h3im : (3 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h3re, h3im, h2re, h2im]
  rw [zeta5_im_eq_sin, zeta5_sq_im', zeta5_pow4_im']
  ring

lemma normSq_A4_at_neg1 : Complex.normSq ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4) =
    ((-7 + 3*√5) / 2)^2 + (2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5))^2 := by
  rw [Complex.normSq_apply, A4_at_neg1_re, A4_at_neg1_im]
  simp only [← sq]

lemma z4_vertex_gt_c_upper : (5 - 3*√5) / 4 > (1 - √5) / 2 := by
  have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)

  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [sqrt5_sq]

  linarith

lemma normSq_A4 : Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) = 16 - 7*√5 := by
  rw [Complex.normSq_apply, A4_re, A4_im]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5

  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring

  have h_im_simp : Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) = Real.sin (π / 5) * (√5 - 3) / 2 := by
    rw [h_sin_double]
    ring

  have h_im_sq : (Real.sin (2 * π / 5) - 2 * Real.sin (π / 5))^2 = (25 - 11*√5) / 8 := by
    rw [h_im_simp]
    have h_sq_mul : (Real.sin (π / 5) * (√5 - 3) / 2)^2 = Real.sin (π / 5)^2 * (√5 - 3)^2 / 4 := by ring
    rw [h_sq_mul, h_sin_sq]
    have h_sqrt5_minus_3_sq : (√5 - 3)^2 = 14 - 6*√5 := by nlinarith [sqrt5_sq]
    rw [h_sqrt5_minus_3_sq]
    nlinarith [sqrt5_sq]

  have h_re_sq : ((-9 + 5*√5) / 4)^2 = (103 - 45*√5) / 8 := by nlinarith [sqrt5_sq]
  simp only [← sq]
  rw [h_re_sq, h_im_sq]
  nlinarith [sqrt5_sq]

lemma seven_minus_3sqrt5_le_three_plus_phi : (7 - 3*√5) / 2 ≤ 3 + φ := by
  have h_sqrt5_nonneg : 0 ≤ √5 := Real.sqrt_nonneg 5
  unfold φ Real.goldenRatio

  linarith

lemma normSq_A4_at_neg1_le_three_plus_phi :
    Complex.normSq ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4) ≤ 3 + φ := by
  rw [normSq_A4_at_neg1]

  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring

  have h_im_simp : 2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5) = Real.sin (π / 5) * (√5 - 1) := by
    rw [h_sin_double]
    ring
  have h_sin_pi5_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by nlinarith [sqrt5_sq]

  have h_im_sq : (2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5))^2 = 5 - 2*√5 := by
    rw [h_im_simp]
    have h_sq_mul : (Real.sin (π / 5) * (√5 - 1))^2 = Real.sin (π / 5)^2 * (√5 - 1)^2 := by ring
    rw [h_sq_mul, h_sin_pi5_sq, h_sqrt5_minus_1_sq]
    nlinarith [sqrt5_sq]

  have h_re_sq : ((-7 + 3*√5) / 2)^2 = (47 - 21*√5) / 2 := by nlinarith [sqrt5_sq]

  calc ((-7 + 3*√5) / 2)^2 + (2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5))^2
      = (47 - 21*√5) / 2 + (5 - 2*√5) := by rw [h_re_sq, h_im_sq]
    _ ≤ (7 + √5) / 2 := by nlinarith [Real.sqrt_nonneg 5]
    _ = 3 + φ := by unfold φ Real.goldenRatio; ring

lemma cross_disk_z4_bound_restricted (c : ℝ) (hc_lo : -1 ≤ c) (hc_hi : c ≤ (1 - √5) / 2) :
    ‖(-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  set A : ℂ := -2 + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := three_plus_phi_pos
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_at_neg1 : ‖A + ((-1 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    have h_neg1 : ((-1 : ℝ) : ℂ) * B = -B := by simp
    rw [h_neg1]
    have h_expr : A + -B = -2 + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 - (1 - ζ₅) := by rw [hA_def, hB_def]; ring
    have h_expr' : A + -B = -3 + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4 := by rw [h_expr]; ring
    rw [← Complex.normSq_eq_norm_sq, h_expr']
    exact normSq_A4_at_neg1_le_three_plus_phi

  have h_mono : ‖A + (c : ℂ) * B‖^2 ≤ ‖A + ((-1 : ℝ) : ℂ) * B‖^2 := by
    rw [hA_def, hB_def]
    simp only [← Complex.normSq_eq_norm_sq]

    have h_normSq_expand : ∀ t : ℝ, Complex.normSq (((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (t : ℂ) * (1 - ζ₅)) =
        Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) +
        2 * t * (((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re +
        t^2 * Complex.normSq (1 - ζ₅) := by
      intro t
      rw [Complex.normSq_add]
      have h_conj_t : starRingEnd ℂ (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      have h_normSq_t : Complex.normSq (t : ℂ) = t^2 := by
        rw [Complex.normSq_ofReal]; ring
      rw [Complex.normSq_mul, h_normSq_t]
      simp only [map_mul, h_conj_t]
      have h_re_scale : (((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * ((t : ℂ) * starRingEnd ℂ (1 - ζ₅))).re =
          t * ((((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)).re) := by
        have h_assoc : ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * ((t : ℂ) * starRingEnd ℂ (1 - ζ₅)) =
            (t : ℂ) * (((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) * starRingEnd ℂ (1 - ζ₅)) := by ring
        rw [h_assoc, Complex.re_ofReal_mul]
      rw [h_re_scale]
      ring

    have h_re_AB := re_A4_mul_conj_B4
    have h_normSq_B := normSq_B4

    rw [h_normSq_expand c, h_normSq_expand (-1)]
    rw [h_re_AB, h_normSq_B]

    have h_c_plus_1_nonneg : 0 ≤ c + 1 := by linarith
    have h_one_minus_c : (1 + √5) / 2 ≤ 1 - c := by linarith

    have h_prod_lower : √5 ≤ (1 - c) * ((5 - √5) / 2) := by
      have h_5_minus_sqrt5_pos : 0 < (5 - √5) / 2 := by nlinarith [Real.sqrt_nonneg 5]
      have h_prod : ((1 + √5) / 2) * ((5 - √5) / 2) = √5 := by nlinarith [sqrt5_sq]
      calc √5 = ((1 + √5) / 2) * ((5 - √5) / 2) := h_prod.symm
        _ ≤ (1 - c) * ((5 - √5) / 2) := by
          apply mul_le_mul_of_nonneg_right h_one_minus_c (le_of_lt h_5_minus_sqrt5_pos)

    have h_second_factor_pos : 0 ≤ -(5*√5 - 10) + (1 - c) * ((5 - √5) / 2) := by
      have h_lower : 10 - 4*√5 ≤ -(5*√5 - 10) + (1 - c) * ((5 - √5) / 2) := by grind
      have h_pos : 0 < 10 - 4*√5 := by nlinarith [sqrt5_sq]
      linarith

    have h_diff_nonneg : 0 ≤ (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*(-1)*((5*√5 - 10) / 2) + (-1)^2*((5 - √5) / 2)) -
         (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*c*((5*√5 - 10) / 2) + c^2*((5 - √5) / 2)) := by
      calc (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*(-1)*((5*√5 - 10) / 2) + (-1)^2*((5 - √5) / 2)) -
           (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*c*((5*√5 - 10) / 2) + c^2*((5 - √5) / 2))
          = (c + 1) * (-(5*√5 - 10) + (1 - c) * ((5 - √5) / 2)) := by ring
        _ ≥ 0 := mul_nonneg h_c_plus_1_nonneg h_second_factor_pos
    linarith
  grind

end TDCSG.CompoundSymmetry.GG5
