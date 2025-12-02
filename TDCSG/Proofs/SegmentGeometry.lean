import TDCSG.Proofs.Points
import TDCSG.Definitions.GroupAction

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions (segment_length translation_length_1 translation_length_2 segmentPoint psi t_F E E' F G ζ₅ zeta5 zeta5Circle zeta5CirclePow zeta5CircleInv φ r_crit)

lemma E_ne_zero : E ≠ 0 := by

  intro h
  unfold E at h
  have h2 : ζ₅^3 * (ζ₅ - 1) = 0 := by
    calc ζ₅^3 * (ζ₅ - 1) = ζ₅^4 - ζ₅^3 := by ring
                     _ = 0 := h
  have h3 : ζ₅^3 ≠ 0 := by
    intro h0
    have : (0 : ℂ) ^ 5 = 1 := by
      have h3_pow : (ζ₅^3)^5 = 1 := by
        calc (ζ₅^3)^5 = ζ₅^15 := by ring
          _ = (ζ₅^5)^3 := by ring
          _ = 1^3 := by rw [zeta5_pow_five]
          _ = 1 := by ring
      calc (0 : ℂ) ^ 5 = (ζ₅^3) ^ 5 := by rw [← h0]
                     _ = 1 := h3_pow
    norm_num at this
  have h4 : ζ₅ - 1 = 0 := by
    exact (mul_eq_zero.mp h2).resolve_left h3
  have : ζ₅ = 1 := by
    have h5 : 1 = ζ₅ := by
      calc 1 = 0 + 1 := by simp
           _ = (ζ₅ - 1) + 1 := by rw [← h4]
           _ = ζ₅ := by ring
    exact h5.symm
  exact zeta5_ne_one this

lemma F_ne_zero : F ≠ 0 := by

  intro h
  have h_psi := F_eq_psi_times_E
  rw [h] at h_psi

  have psi_ne_zero' : psi ≠ 0 := psi_ne_zero
  have : E = 0 := by
    rw [show (0 : ℂ) = psi • 0 by simp] at h_psi
    have eq : psi • (0 : ℂ) = psi • E := by rw [h_psi]
    have h_sub : psi • ((0 : ℂ) - E) = 0 := by
      calc psi • ((0 : ℂ) - E)
          = psi • (0 : ℂ) - psi • E := by rw [← smul_sub]
        _ = psi • E - psi • E := by rw [eq]
        _ = 0 := by ring
    rw [smul_eq_zero] at h_sub
    cases h_sub with
    | inl h => exact absurd h psi_ne_zero'
    | inr h =>
      simp only [sub_eq_zero] at h
      exact h.symm
  exact E_ne_zero this

lemma segment_ratio_is_golden :
    segment_length / translation_length_1 = Real.goldenRatio := by
  unfold segment_length translation_length_1

  have h_seg : ‖E - E'‖ = 2 * ‖E‖ := by
    unfold E'
    rw [show E - (-E) = (2 : ℕ) • E by simp [two_smul]]
    rw [show (2 : ℕ) • E = (2 : ℝ) • E by norm_cast]
    rw [norm_smul]
    norm_num

  have h_trans : ‖F - (-F)‖ = 2 * ‖F‖ := by
    rw [show F - (-F) = (2 : ℕ) • F by simp [two_smul]]
    rw [show (2 : ℕ) • F = (2 : ℝ) • F by norm_cast]
    rw [norm_smul]
    norm_num

  rw [h_seg, h_trans]

  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

  have h_F_norm_ne_zero : ‖F‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr F_ne_zero

  have h_E_norm_ne_zero : ‖E‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr E_ne_zero

  have h_F_eq : F = psi • E := F_eq_psi_times_E

  have h_F_norm : ‖F‖ = |psi| * ‖E‖ := by
    rw [h_F_eq, norm_smul]
    rfl

  rw [h_F_norm]

  have h_simplify : ‖E‖ / (|psi| * ‖E‖) = 1 / |psi| := by
    field_simp [h_E_norm_ne_zero]

  rw [h_simplify]

  have psi_pos' : 0 < psi := psi_pos

  have abs_psi : |psi| = psi := by
    exact abs_of_pos psi_pos'

  rw [abs_psi]

  rw [psi_eq, one_div, inv_div]
  rw [show (2 : ℝ) / (Real.sqrt 5 - 1) = Real.goldenRatio by
    unfold Real.goldenRatio
    have sqrt5_gt_one' : 1 < Real.sqrt 5 := sqrt5_gt_one
    field_simp [ne_of_gt (by linarith : (0 : ℝ) < Real.sqrt 5 - 1)]
    have h1 : (2 : ℝ) ^ 2 = 4 := by ring
    have h2 : (4 : ℝ) = Real.sqrt 5 ^ 2 - 1 := by rw [sqrt5_sq]; ring
    have h3 : Real.sqrt 5 ^ 2 - 1 = (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) := by ring
    have h4 : (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) = (Real.sqrt 5 - 1) * (1 + Real.sqrt 5) := by ring
    calc 2 ^ 2 = 4 := h1
      _ = Real.sqrt 5 ^ 2 - 1 := h2
      _ = (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) := h3
      _ = (Real.sqrt 5 - 1) * (1 + Real.sqrt 5) := h4]

lemma translations_irrational : ∀ (q r : ℤ),
    q ≠ 0 ∨ r ≠ 0 →
    (q : ℝ) * translation_length_1 + (r : ℝ) * translation_length_2 ≠ 0 := by
  intro q r h_nonzero

  have h_tl1 : translation_length_1 = (Real.sqrt 5 - 1) * ‖E‖ := by
    unfold translation_length_1
    rw [show F - (-F) = (2 : ℕ) • F by simp [two_smul]]
    rw [show (2 : ℕ) • F = (2 : ℝ) • F by norm_cast]
    rw [norm_smul, F_eq_psi_times_E, norm_smul]
    rw [psi_eq]
    have sqrt5_gt_1 : 1 < Real.sqrt 5 := by
      calc (1 : ℝ) = Real.sqrt 1 := by norm_num
        _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h_psi_pos : 0 < (Real.sqrt 5 - 1) / 2 := by linarith
    simp only [Real.norm_of_nonneg (le_of_lt h_psi_pos), Real.norm_two]
    ring

  have h_tl2 : translation_length_2 = (3 - Real.sqrt 5) * ‖E‖ := by
    unfold translation_length_2
    rw [G_eq_coeff_times_E]
    rw [show E - (Real.sqrt 5 - 2) • E = (1 - (Real.sqrt 5 - 2)) • E by simp [sub_smul, one_smul]]
    rw [norm_smul]
    have h_coeff : 1 - (Real.sqrt 5 - 2) = 3 - Real.sqrt 5 := by ring
    rw [h_coeff]
    have sqrt5_lt_3 : Real.sqrt 5 < 3 := by
      have h1 : Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      calc Real.sqrt 5 < Real.sqrt 9 := h1
        _ = Real.sqrt (3 ^ 2) := by norm_num
        _ = 3 := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)
    have h_pos : 0 < 3 - Real.sqrt 5 := by linarith
    simp [abs_of_pos h_pos]

  rw [h_tl1, h_tl2]

  have h_factor : (q : ℝ) * ((Real.sqrt 5 - 1) * ‖E‖) + (r : ℝ) * ((3 - Real.sqrt 5) * ‖E‖) =
                  ‖E‖ * ((q : ℝ) * (Real.sqrt 5 - 1) + (r : ℝ) * (3 - Real.sqrt 5)) := by
    ring
  rw [h_factor]

  have h_E_norm_pos : 0 < ‖E‖ := norm_pos_iff.mpr E_ne_zero

  intro h_contra
  have h_inner : (q : ℝ) * (Real.sqrt 5 - 1) + (r : ℝ) * (3 - Real.sqrt 5) = 0 := by
    have := mul_eq_zero.mp h_contra
    cases this with
    | inl h => exfalso; linarith
    | inr h => exact h

  have h_rearrange : ((3 * r - q) : ℝ) + (q - r : ℝ) * Real.sqrt 5 = 0 := by
    calc ((3 * r - q) : ℝ) + (q - r : ℝ) * Real.sqrt 5
        = (3 * (r : ℝ) - (q : ℝ)) + ((q : ℝ) - (r : ℝ)) * Real.sqrt 5 := by simp
      _ = 3 * (r : ℝ) - (q : ℝ) + (q : ℝ) * Real.sqrt 5 - (r : ℝ) * Real.sqrt 5 := by ring
      _ = (q : ℝ) * (Real.sqrt 5 - 1) + (r : ℝ) * (3 - Real.sqrt 5) := by ring
      _ = 0 := h_inner

  by_cases h_eq : q = r
  ·

    rw [h_eq] at h_rearrange
    simp at h_rearrange
    have r_zero : r = 0 := by
      have : (r : ℝ) * 2 = 0 := by linarith
      have : (r : ℝ) = 0 := by linarith
      simp at this
      exact this
    rw [r_zero] at h_eq
    have q_zero : q = 0 := h_eq

    cases h_nonzero with
    | inl h => exact h q_zero
    | inr h => exact h r_zero
  ·

    have h_r_ne_q : (r : ℝ) ≠ (q : ℝ) := by
      intro h_contra_eq
      exact h_eq (Int.cast_injective h_contra_eq.symm)
    have h_qr_nonzero : (q : ℝ) - (r : ℝ) ≠ 0 := by
      intro h_bad
      apply h_r_ne_q
      linarith
    have h_sqrt5 : Real.sqrt 5 = ((q : ℝ) - 3 * (r : ℝ)) / ((q : ℝ) - (r : ℝ)) := by
      field_simp [h_qr_nonzero]

      linarith

    have h_sqrt5_irrational : Irrational (Real.sqrt 5) := by
      have : Nat.Prime 5 := by norm_num
      exact this.irrational_sqrt

    apply h_sqrt5_irrational
    rw [h_sqrt5]

    use ((q - 3 * r : ℤ) : ℚ) / ((q - r : ℤ) : ℚ)
    push_cast
    rfl

theorem segmentPoint_injective : Function.Injective segmentPoint := by
  intro t₁ t₂ h
  unfold segmentPoint at h
  have hne : E - E' ≠ 0 := by
    unfold E'
    simp only [sub_neg_eq_add, ne_eq]
    have hE_ne : E ≠ 0 := E_ne_zero
    intro h
    apply hE_ne
    calc E = (E + E) / 2 := by ring
         _ = 0 / 2 := by rw [h]
         _ = 0 := by ring
  have : t₁ • (E - E') = t₂ • (E - E') := by
    have h' : E' + t₁ • (E - E') = E' + t₂ • (E - E') := h
    exact add_left_cancel h'

  by_contra h_ne
  have : t₁ • (E - E') - t₂ • (E - E') = 0 := by
    rw [this]; ring
  rw [← sub_smul] at this
  have hsub_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have : E - E' = 0 := by
    have h_smul : (t₁ - t₂) • (E - E') = 0 := this
    exact smul_eq_zero.mp h_smul |>.resolve_left hsub_ne
  exact hne this

lemma E'_on_right_disk_boundary : ‖E' - 1‖ = r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (1 : ℂ)) = -(E + 1) by ring]
  rw [norm_neg]
  exact E_on_left_disk_boundary

lemma E'_in_left_disk : ‖E' - (-1)‖ ≤ r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (-1 : ℂ)) = -(E - 1) by ring]
  rw [norm_neg]
  exact E_in_right_disk

lemma E_re_pos : 0 < E.re := by
  rw [E_re]
  have sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  linarith

lemma E'_re_neg : E'.re < 0 := by
  unfold E'
  simp [E_re_pos]

lemma segment_in_disk_intersection (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    let p := E' + t • (E - E')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  have hp_segment : p ∈ segment ℝ E' E := by
    use (1 - t), t
    constructor; · linarith [ht.1]
    constructor; · exact ht.1
    constructor; · linarith [ht.2]
    calc (1 - t) • E' + t • E
        = E' - t • E' + t • E := by
          rw [sub_smul, one_smul]
      _ = E' + (t • E - t • E') := by
          ring
      _ = E' + t • (E - E') := by
          rw [smul_sub]
  constructor
  · have h_E'_in_left :
        E' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      exact E'_in_left_disk
    have h_E_in_left :
        E ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      rw [show (E - (-1) : ℂ) = E + 1 by ring]
      exact E_on_left_disk_boundary.le
    have h_convex : Convex ℝ
        (Metric.closedBall ((-1) : ℂ) r_crit) :=
      convex_closedBall ((-1) : ℂ) r_crit
    have h_segment_subset :
        segment ℝ E' E ⊆
          Metric.closedBall ((-1) : ℂ) r_crit :=
      h_convex.segment_subset h_E'_in_left h_E_in_left
    have hp_in_left :
        p ∈ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_left
    simp only [dist_eq_norm] at hp_in_left
    rw [show (p - (-1) : ℂ) = p + 1 by ring] at hp_in_left
    exact hp_in_left
  · have h_E'_in_right :
        E' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      exact E'_on_right_disk_boundary.le
    have h_E_in_right :
        E ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      rw [show (E - 1 : ℂ) = E - 1 by ring]
      exact E_in_right_disk
    have h_convex : Convex ℝ
        (Metric.closedBall (1 : ℂ) r_crit) :=
      convex_closedBall (1 : ℂ) r_crit
    have h_segment_subset :
        segment ℝ E' E ⊆ Metric.closedBall (1 : ℂ) r_crit :=
      h_convex.segment_subset h_E'_in_right h_E_in_right
    have hp_in_right :
        p ∈ Metric.closedBall (1 : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_right
    simp only [dist_eq_norm] at hp_in_right
    exact hp_in_right

end TDCSG.CompoundSymmetry.GG5
