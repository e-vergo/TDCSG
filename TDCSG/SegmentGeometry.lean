/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Conversions
import TDCSG.Points

/-!
# Segment Geometry for GG(5,5)

Defines segment lengths, ratios, and proves key irrationality results.

The conversion functions (toR2, E_R2, etc.) are imported from TDCSG.Definitions.Conversions.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-! ### Helper Lemmas for F and G Relationships -/

/-- Helper: ζ₅ + ζ₅⁴ equals psi = (√5-1)/2. -/
private lemma zeta5_plus_zeta5_fourth' : ζ₅ + ζ₅^4 = psi := by
  -- ζ₅ + ζ₅⁴ = e^(2πi/5) + e^(-2πi/5) = 2•cos(2π/5)
  conv_lhs => rw [show ζ₅^4 = starRingEnd ℂ ζ₅ from zeta5_conj.symm]
  have h1 : ζ₅ + starRingEnd ℂ ζ₅ = (2 * ζ₅.re : ℝ) := Complex.add_conj ζ₅
  rw [h1]
  have h2 : ζ₅.re = Real.cos (2 * π / 5) := by
    have h := zeta5_eq
    rw [h]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2, cos_two_pi_fifth]
  unfold psi Real.goldenRatio
  push_cast
  ring

/-- F equals psi times E: F = psi • E where psi = (√5-1)/2. -/
lemma F_eq_psi_times_E : F = psi • E := by
  unfold F E
  -- Strategy: Use the factorization (ζ₅ + ζ₅⁴)(ζ₅ - ζ₅²) = 1 - ζ₅ + ζ₅² - ζ₅³
  have h1 := zeta5_plus_zeta5_fourth'
  -- Compute: (ζ₅ + ζ₅⁴)(ζ₅ - ζ₅²) = ζ₅² - ζ₅³ + ζ₅⁵ - ζ₅⁶
  have h_mult : (ζ₅ + ζ₅^4) * (ζ₅ - ζ₅^2) = ζ₅^2 - ζ₅^3 + ζ₅^5 - ζ₅^6 := by ring
  rw [zeta5_pow_five] at h_mult
  have h6 : ζ₅^6 = ζ₅ := by
    calc ζ₅^6 = ζ₅^5 * ζ₅ := by ring
      _ = 1 * ζ₅ := by rw [zeta5_pow_five]
      _ = ζ₅ := by ring
  rw [h6] at h_mult
  rw [h1] at h_mult
  rw [show ζ₅^2 - ζ₅^3 + (1 : ℂ) - ζ₅ = 1 - ζ₅ + ζ₅^2 - ζ₅^3 by ring] at h_mult
  -- Convert from multiplication to scalar multiplication
  rw [← smul_eq_mul] at h_mult
  exact h_mult.symm

/-- G equals (√5 - 2) times E. -/
lemma G_eq_coeff_times_E : G = ((Real.sqrt 5 - 2) : ℝ) • E := by
  -- Use G = 2F - E and F = psi • E
  unfold G
  rw [F_eq_psi_times_E]
  -- Goal: 2 * psi • E - E = (√5 - 2) • E
  -- First prove the key coefficient identity
  have h_coeff : 2 * psi - 1 = Real.sqrt 5 - 2 := by
    unfold psi
    field_simp
    ring
  -- Now prove the main goal
  -- Convert 2 * psi • E to (2 * psi) • E first
  have h_smul : (2 : ℂ) * psi • E = ((2 : ℝ) * psi) • E := by
    rw [mul_smul]
    simp [ofReal_ofNat]
  rw [h_smul]
  -- Convert to smul form
  rw [show E = (1 : ℝ) • E by simp]
  simp only [smul_smul, mul_one]
  rw [← sub_smul]
  rw [h_coeff]

/-! ### Translation Lengths -/

-- The definitions translation_length_1, translation_length_2, and segment_length
-- are imported from TDCSG.Definitions.Conversions

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
  have psi_ne_zero : psi ≠ 0 := by
    unfold psi
    apply div_ne_zero
    · linarith [sqrt5_gt_one]
    · norm_num
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
    | inl h => exact absurd h psi_ne_zero
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
  have psi_pos : 0 < psi := by
    unfold psi
    apply div_pos
    · linarith [sqrt5_gt_one]
    · norm_num

  have abs_psi : |psi| = psi := by
    exact abs_of_pos psi_pos

  rw [abs_psi]

  -- Now: 1 / psi = 1 / ((√5-1)/2) = 2/(√5-1)
  -- Rationalize: 2/(√5-1) = 2(√5+1)/((√5-1)(√5+1)) = 2(√5+1)/4 = (√5+1)/2 = φ
  unfold psi
  rw [one_div, inv_div]
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
    unfold psi
    have sqrt5_gt_1 : 1 < Real.sqrt 5 := by
      calc (1 : ℝ) = Real.sqrt 1 := by norm_num
        _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h_psi_pos : 0 < (Real.sqrt 5 - 1) / 2 := by linarith
    have sqrt5_nonneg : 0 ≤ Real.sqrt 5 - 1 := by linarith
    simp [abs_of_nonneg sqrt5_nonneg]
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

/-! ### Conversion to ℝ² -/

-- The conversion functions (toR2, E_R2, E'_R2, F_R2, G_R2) are now in TDCSG.Definitions.Conversions

end TDCSG.CompoundSymmetry.GG5
