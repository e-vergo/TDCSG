/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.Points
import TDCSG.Definitions.GroupAction

/-!
# Segment Geometry for GG(5,5)

Defines segment lengths, ratios, disk intersection, and rotation correspondence.

The segment definitions are imported from TDCSG.Definitions.Points.
The generator actions are imported from TDCSG.Definitions.GroupAction.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-! ### Translation Lengths -/

/-- E is nonzero. -/
lemma E_ne_zero : E ≠ 0 := by
  -- E = ζ₅ - ζ₅². If E = 0, then ζ₅ = ζ₅², so ζ₅(1 - ζ₅) = 0.
  -- Since ζ₅ ≠ 0 (it's a root of unity), we have ζ₅ = 1, contradicting zeta5_ne_one.
  intro h
  unfold E at h
  have h2 : ζ₅ * (1 - ζ₅) = 0 := by
    calc ζ₅ * (1 - ζ₅) = ζ₅ - ζ₅^2 := by ring
                     _ = 0 := h
  have h3 : ζ₅ ≠ 0 := by
    intro h0
    have : (0 : ℂ) ^ 5 = 1 := by
      calc (0 : ℂ) ^ 5 = ζ₅ ^ 5 := by rw [← h0]
                     _ = 1 := zeta5_pow_five
    norm_num at this
  have h4 : 1 - ζ₅ = 0 := by
    exact (mul_eq_zero.mp h2).resolve_left h3
  have : ζ₅ = 1 := by
    have h5 : 1 = ζ₅ := by
      calc 1 = 1 - 0 := by simp
           _ = 1 - (1 - ζ₅) := by rw [← h4]
           _ = ζ₅ := by simp
    exact h5.symm
  exact zeta5_ne_one this

/-- F is nonzero. -/
lemma F_ne_zero : F ≠ 0 := by
  -- If F = 0, then from F = psi • E, we get E = 0, contradicting E_ne_zero
  intro h
  have h_psi := F_eq_psi_times_E
  rw [h] at h_psi
  -- Need to show psi ≠ 0 to get E = 0
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

/-- The ratio equals the golden ratio. -/
lemma segment_ratio_is_golden :
    segment_length / translation_length_1 = Real.goldenRatio := by
  unfold segment_length translation_length_1

  -- segment_length = ‖E - E'‖ = ‖2•E‖ = 2‖E‖
  have h_seg : ‖E - E'‖ = 2 * ‖E‖ := by
    unfold E'
    rw [show E - (-E) = (2 : ℕ) • E by simp [two_smul]]
    rw [show (2 : ℕ) • E = (2 : ℝ) • E by norm_cast]
    rw [norm_smul]
    norm_num

  -- translation_length_1 = ‖F - (-F)‖ = ‖2•F‖ = 2‖F‖
  have h_trans : ‖F - (-F)‖ = 2 * ‖F‖ := by
    rw [show F - (-F) = (2 : ℕ) • F by simp [two_smul]]
    rw [show (2 : ℕ) • F = (2 : ℝ) • F by norm_cast]
    rw [norm_smul]
    norm_num

  rw [h_seg, h_trans]

  -- Simplify: (2 * ‖E‖) / (2 * ‖F‖) = ‖E‖ / ‖F‖
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

  -- We need F ≠ 0 and E ≠ 0
  have h_F_norm_ne_zero : ‖F‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr F_ne_zero

  have h_E_norm_ne_zero : ‖E‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr E_ne_zero

  -- Use F = psi • E (from F_eq_psi_times_E)
  have h_F_eq : F = psi • E := F_eq_psi_times_E

  -- Compute ‖F‖ = |psi| * ‖E‖
  have h_F_norm : ‖F‖ = |psi| * ‖E‖ := by
    rw [h_F_eq, norm_smul]
    rfl

  rw [h_F_norm]

  -- Simplify: ‖E‖ / (|psi| * ‖E‖) = 1 / |psi|
  have h_simplify : ‖E‖ / (|psi| * ‖E‖) = 1 / |psi| := by
    field_simp [h_E_norm_ne_zero]

  rw [h_simplify]

  -- Since psi > 0, we have |psi| = psi
  have psi_pos' : 0 < psi := psi_pos

  have abs_psi : |psi| = psi := by
    exact abs_of_pos psi_pos'

  rw [abs_psi]

  -- Now: 1 / psi = 1 / ((√5-1)/2) = 2/(√5-1)
  -- Rationalize: 2/(√5-1) = 2(√5+1)/((√5-1)(√5+1)) = 2(√5+1)/4 = (√5+1)/2 = φ
  rw [psi_eq, one_div, inv_div]
  rw [show (2 : ℝ) / (Real.sqrt 5 - 1) = Real.goldenRatio by
    unfold Real.goldenRatio
    have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have sqrt5_gt_one' : 1 < Real.sqrt 5 := sqrt5_gt_one
    field_simp [ne_of_gt (by linarith : (0 : ℝ) < Real.sqrt 5 - 1)]
    have h1 : (2 : ℝ) ^ 2 = 4 := by ring
    have h2 : (4 : ℝ) = Real.sqrt 5 ^ 2 - 1 := by rw [h_sqrt5_sq]; ring
    have h3 : Real.sqrt 5 ^ 2 - 1 = (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) := by ring
    have h4 : (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) = (Real.sqrt 5 - 1) * (1 + Real.sqrt 5) := by ring
    calc 2 ^ 2 = 4 := h1
      _ = Real.sqrt 5 ^ 2 - 1 := h2
      _ = (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) := h3
      _ = (Real.sqrt 5 - 1) * (1 + Real.sqrt 5) := h4]

/-- The two translation lengths are not rationally related.
    This is the corrected version that excludes segment_length to avoid the
    counterexample p=-1, q=1, r=1 (since segment_length = φ • translation_length_1). -/
lemma translations_irrational : ∀ (q r : ℤ),
    q ≠ 0 ∨ r ≠ 0 →
    (q : ℝ) * translation_length_1 + (r : ℝ) * translation_length_2 ≠ 0 := by
  intro q r h_nonzero

  -- Step 1: Express translation_length_1 in terms of ‖E‖
  -- translation_length_1 = ‖F - (-F)‖ = 2‖F‖ = 2|psi|‖E‖ = (√5 - 1)‖E‖
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

  -- Step 2: Express translation_length_2 in terms of ‖E‖
  -- translation_length_2 = ‖E - G‖ = ‖E - (√5 - 2)•E‖ = ‖(3 - √5)•E‖ = (3 - √5)‖E‖
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

  -- Step 3: Substitute into the linear combination and factor out ‖E‖
  rw [h_tl1, h_tl2]
  -- Goal: (q : ℝ) * ((√5 - 1) * ‖E‖) + (r : ℝ) * ((3 - √5) * ‖E‖) ≠ 0
  have h_factor : (q : ℝ) * ((Real.sqrt 5 - 1) * ‖E‖) + (r : ℝ) * ((3 - Real.sqrt 5) * ‖E‖) =
                  ‖E‖ * ((q : ℝ) * (Real.sqrt 5 - 1) + (r : ℝ) * (3 - Real.sqrt 5)) := by
    ring
  rw [h_factor]

  -- Step 4: Show ‖E‖ ≠ 0
  have h_E_norm_pos : 0 < ‖E‖ := norm_pos_iff.mpr E_ne_zero

  -- Step 5: Reduce to showing the inner expression ≠ 0
  intro h_contra
  have h_inner : (q : ℝ) * (Real.sqrt 5 - 1) + (r : ℝ) * (3 - Real.sqrt 5) = 0 := by
    have := mul_eq_zero.mp h_contra
    cases this with
    | inl h => exfalso; linarith
    | inr h => exact h

  -- Step 6: Rearrange to get (3r - q) + (q - r)√5 = 0
  have h_rearrange : ((3 * r - q) : ℝ) + (q - r : ℝ) * Real.sqrt 5 = 0 := by
    calc ((3 * r - q) : ℝ) + (q - r : ℝ) * Real.sqrt 5
        = (3 * (r : ℝ) - (q : ℝ)) + ((q : ℝ) - (r : ℝ)) * Real.sqrt 5 := by simp
      _ = 3 * (r : ℝ) - (q : ℝ) + (q : ℝ) * Real.sqrt 5 - (r : ℝ) * Real.sqrt 5 := by ring
      _ = (q : ℝ) * (Real.sqrt 5 - 1) + (r : ℝ) * (3 - Real.sqrt 5) := by ring
      _ = 0 := h_inner

  -- Step 7: Show this implies √5 is rational (contradiction)
  by_cases h_eq : q = r
  · -- Case: q = r
    -- Then (3r - q) + (q - r)√5 = 2r + 0 = 0, so r = 0, hence q = 0
    rw [h_eq] at h_rearrange
    simp at h_rearrange
    have r_zero : r = 0 := by
      have : (r : ℝ) * 2 = 0 := by linarith
      have : (r : ℝ) = 0 := by linarith
      simp at this
      exact this
    rw [r_zero] at h_eq
    have q_zero : q = 0 := h_eq
    -- But this contradicts h_nonzero
    cases h_nonzero with
    | inl h => exact h q_zero
    | inr h => exact h r_zero
  · -- Case: q ≠ r
    -- Then √5 = (q - 3r) / (q - r), which is rational
    have h_r_ne_q : (r : ℝ) ≠ (q : ℝ) := by
      intro h_contra_eq
      exact h_eq (Int.cast_injective h_contra_eq.symm)
    have h_qr_nonzero : (q : ℝ) - (r : ℝ) ≠ 0 := by
      intro h_bad
      apply h_r_ne_q
      linarith
    have h_sqrt5 : Real.sqrt 5 = ((q : ℝ) - 3 * (r : ℝ)) / ((q : ℝ) - (r : ℝ)) := by
      field_simp [h_qr_nonzero]
      -- Goal: (q - r) * √5 = q - 3r
      -- From h_rearrange: 3r - q + (q - r)√5 = 0
      -- Rearranging: (q - r)√5 = q - 3r
      linarith
    -- But √5 is irrational
    have h_sqrt5_irrational : Irrational (Real.sqrt 5) := by
      have : Nat.Prime 5 := by norm_num
      exact this.irrational_sqrt
    -- Contradiction: √5 is both rational and irrational
    apply h_sqrt5_irrational
    rw [h_sqrt5]
    -- Show that (q - 3r) / (q - r) is in the range of Rat.cast
    use ((q - 3 * r : ℤ) : ℚ) / ((q - r : ℤ) : ℚ)
    push_cast
    rfl

/-! ### Segment Parameterization Injectivity -/

/-- The segment parameterization is injective: different parameters give different points. -/
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
  -- From t₁ • v = t₂ • v with v ≠ 0, conclude t₁ = t₂
  by_contra h_ne
  have : t₁ • (E - E') - t₂ • (E - E') = 0 := by
    rw [this]; ring
  rw [← sub_smul] at this
  have hsub_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have : E - E' = 0 := by
    have h_smul : (t₁ - t₂) • (E - E') = 0 := this
    exact smul_eq_zero.mp h_smul |>.resolve_left hsub_ne
  exact hne this

/-- The Plane parameterization is also injective. -/
theorem segmentPointPlane_injective : Function.Injective segmentPointPlane := by
  intro t₁ t₂ h
  apply segmentPoint_injective
  unfold segmentPointPlane toPlane at h
  -- If ![z₁.re, z₁.im] = ![z₂.re, z₂.im], then z₁ = z₂
  have hre : (segmentPoint t₁).re = (segmentPoint t₂).re := by
    have := congrFun h 0
    simp only [Matrix.cons_val_zero] at this
    exact this
  have him : (segmentPoint t₁).im = (segmentPoint t₂).im := by
    have := congrFun h 1
    simp only [Matrix.cons_val_one] at this
    exact this
  exact Complex.ext hre him

/-! ### Disk Intersection Lemmas -/

/-- E' is on the RIGHT disk boundary (since E is on left disk boundary). -/
lemma E'_on_right_disk_boundary : ‖E' - 1‖ = r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (1 : ℂ)) = -(E + 1) by ring]
  rw [norm_neg]
  exact E_on_left_disk_boundary

/-- E' is in the LEFT disk (since E is in right disk). -/
lemma E'_in_left_disk : ‖E' - (-1)‖ ≤ r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (-1 : ℂ)) = -(E - 1) by ring]
  rw [norm_neg]
  exact E_in_right_disk

/-- Compute real part of E in trigonometric form -/
private lemma E_re_trig : E.re = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
  unfold E
  have h1 := zeta5_eq
  have h2 := zeta5_sq_eq
  calc (ζ₅ - ζ₅ ^ 2).re
      = ((↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5))) -
        (↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5)))).re := by
        rw [← h1, ← h2]
    _ = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring

/-- Point E has positive real part. -/
lemma E_re_pos : 0 < E.re := by
  rw [E_re_trig, cos_four_pi_fifth, cos_two_pi_fifth, Real.cos_pi_div_five]
  unfold Real.goldenRatio
  have h : ((1 + Real.sqrt 5) / 2 - 1) / 2 - -((1 + Real.sqrt 5) / 4) = Real.sqrt 5 / 2 := by
    field_simp; ring
  rw [h]
  have sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  linarith

/-- Point E' has negative real part. -/
lemma E'_re_neg : E'.re < 0 := by
  unfold E'
  simp [E_re_pos]

/-- Points on segment E'E lie in the disk intersection. -/
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

/-! ### Complex Multiplication and Rotation Correspondence -/

/-- Complex multiplication as a matrix. -/
lemma complex_mul_as_matrix (a z : ℂ) :
    toPlane (a * z) = applyMatrix !![a.re, -a.im; a.im, a.re] (toPlane z) := by
  unfold toPlane applyMatrix
  ext i
  fin_cases i <;> simp [Complex.mul_re, Complex.mul_im, Fin.sum_univ_two] <;> ring

/-- Rotation in ℂ by ζ₅ corresponds to rotateAroundPoint in Plane. -/
theorem zeta5_rotation_eq_rotateAroundPoint (z c : ℂ) :
    toPlane (c + ζ₅ * (z - c)) = rotateAroundPoint (toPlane c) (2 * π / 5) (toPlane z) := by
  unfold rotateAroundPoint
  rw [toPlane_add]
  congr 1
  rw [← toPlane_sub]
  rw [complex_mul_as_matrix]
  congr 1
  unfold rotationMatrix
  rw [zeta5_re_eq_cos, zeta5_im_eq_sin]

/-- Segment points are in the left disk at r_crit. -/
lemma segmentPointPlane_in_leftDisk (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    segmentPointPlane t ∈ leftDisk r_crit := by
  unfold leftDisk closedDisk
  rw [Metric.mem_closedBall]
  rw [leftCenter_eq_toPlane]
  unfold segmentPointPlane
  rw [toPlane_dist_eq_complex_norm]
  rw [show segmentPoint t - (-1 : ℂ) = segmentPoint t + 1 by ring]
  have h_mem := segment_in_disk_intersection t ⟨ht.1, le_of_lt ht.2⟩
  unfold segmentPoint at h_mem ⊢
  exact h_mem.1

/-- Segment points are in the right disk at r_crit. -/
lemma segmentPointPlane_in_rightDisk (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    segmentPointPlane t ∈ rightDisk r_crit := by
  unfold rightDisk closedDisk
  rw [Metric.mem_closedBall]
  rw [rightCenter_eq_toPlane]
  unfold segmentPointPlane
  rw [toPlane_dist_eq_complex_norm]
  rw [show segmentPoint t - (1 : ℂ) = segmentPoint t - 1 by ring]
  have h_mem := segment_in_disk_intersection t ⟨ht.1, le_of_lt ht.2⟩
  unfold segmentPoint at h_mem ⊢
  exact h_mem.2

/-! ### Generator Actions in Complex Form -/

/-- genA on a point in the left disk equals rotation by ζ₅ about -1 in complex coords. -/
lemma genA_eq_zeta5_rotation (z : ℂ) (hz : toPlane z ∈ leftDisk r_crit) :
    genA r_crit (toPlane z) = toPlane ((-1 : ℂ) + ζ₅ * (z - (-1))) := by
  unfold genA
  rw [if_pos hz]
  rw [leftCenter_eq_toPlane]
  exact (zeta5_rotation_eq_rotateAroundPoint z (-1)).symm

/-- genB on a point in the right disk equals rotation by ζ₅ about 1 in complex coords. -/
lemma genB_eq_zeta5_rotation (z : ℂ) (hz : toPlane z ∈ rightDisk r_crit) :
    genB r_crit (toPlane z) = toPlane ((1 : ℂ) + ζ₅ * (z - 1)) := by
  unfold genB
  rw [if_pos hz]
  rw [rightCenter_eq_toPlane]
  exact (zeta5_rotation_eq_rotateAroundPoint z 1).symm

/-- A⁻¹ = A⁴ means multiplying by ζ₅⁴. -/
lemma genA_inv_eq_zeta5_pow4_rotation (z : ℂ)
    (hz : toPlane z ∈ leftDisk r_crit)
    (hz' : toPlane ((-1 : ℂ) + ζ₅ * (z + 1)) ∈ leftDisk r_crit)
    (hz'' : toPlane ((-1 : ℂ) + ζ₅^2 * (z + 1)) ∈ leftDisk r_crit)
    (hz''' : toPlane ((-1 : ℂ) + ζ₅^3 * (z + 1)) ∈ leftDisk r_crit) :
    genA r_crit (genA r_crit (genA r_crit
      (genA r_crit (toPlane z)))) =
    toPlane ((-1 : ℂ) + ζ₅^4 * (z + 1)) := by
  rw [genA_eq_zeta5_rotation z hz]
  rw [show -1 + ζ₅ * (z - -1) = -1 + ζ₅ * (z + 1) by ring]
  rw [genA_eq_zeta5_rotation _ hz']
  rw [show -1 + ζ₅ * (-1 + ζ₅ * (z + 1) - -1) = -1 + ζ₅^2 * (z + 1) by ring]
  rw [genA_eq_zeta5_rotation _ hz'']
  rw [show -1 + ζ₅ * (-1 + ζ₅ ^ 2 * (z + 1) - -1) = -1 + ζ₅^3 * (z + 1) by ring]
  rw [genA_eq_zeta5_rotation _ hz''']
  rw [show -1 + ζ₅ * (-1 + ζ₅ ^ 3 * (z + 1) - -1) = -1 + ζ₅^4 * (z + 1) by ring]

/-- B⁻¹ = B⁴ means multiplying by ζ₅⁴. -/
lemma genB_inv_eq_zeta5_pow4_rotation (z : ℂ)
    (hz : toPlane z ∈ rightDisk r_crit)
    (hz' : toPlane ((1 : ℂ) + ζ₅ * (z - 1)) ∈ rightDisk r_crit)
    (hz'' : toPlane ((1 : ℂ) + ζ₅^2 * (z - 1)) ∈ rightDisk r_crit)
    (hz''' : toPlane ((1 : ℂ) + ζ₅^3 * (z - 1)) ∈ rightDisk r_crit) :
    genB r_crit (genB r_crit (genB r_crit
      (genB r_crit (toPlane z)))) =
    toPlane ((1 : ℂ) + ζ₅^4 * (z - 1)) := by
  rw [genB_eq_zeta5_rotation z hz]
  rw [genB_eq_zeta5_rotation _ hz']
  rw [show 1 + ζ₅ * (1 + ζ₅ * (z - 1) - 1) = 1 + ζ₅^2 * (z - 1) by ring]
  rw [genB_eq_zeta5_rotation _ hz'']
  rw [show 1 + ζ₅ * (1 + ζ₅ ^ 2 * (z - 1) - 1) = 1 + ζ₅^3 * (z - 1) by ring]
  rw [genB_eq_zeta5_rotation _ hz''']
  rw [show 1 + ζ₅ * (1 + ζ₅ ^ 3 * (z - 1) - 1) = 1 + ζ₅^4 * (z - 1) by ring]

end TDCSG.CompoundSymmetry.GG5
