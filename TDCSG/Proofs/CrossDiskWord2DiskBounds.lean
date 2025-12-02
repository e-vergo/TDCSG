/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

import TDCSG.Proofs.CrossDiskWord3Helpers
import TDCSG.Proofs.RotationFormulas

set_option maxHeartbeats 400000

/-!
# Cross-disk bound theorems for word2

This file contains the cross-disk bound theorems for the word2 parameter range
c in [(1-sqrt(5))/2, 2-sqrt(5)].

word2 = [A^{-1}, B^{-1}, A^{-1}, B^{-1}, B^{-1}]

For interval 1, x in [length1, length1 + length2), we have c = 2x - 1 in this range.

## Main results

- `cross_disk_w2_z1_bound`: z1 intermediate point stays within r_crit (rightDisk)
- `cross_disk_w2_z2_bound`: z2 intermediate point stays within r_crit (leftDisk)
- `cross_disk_w2_z3_bound`: z3 intermediate point stays within r_crit (rightDisk)
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real
open TDCSG.Definitions hiding φ r_crit

/-- The lower bound for c in interval 1 (word2): (1 - √5)/2 = goldenConj -/
private noncomputable abbrev c_lower_word2 : ℝ := Real.goldenConj

/-- The upper bound for c in interval 1 (word2): 2 - √5 -/
private noncomputable abbrev c_upper_word2 : ℝ := 2 - √5

/-- The lower bound for c in interval 2 (word3): 2 - √5 (equals c_upper_word2) -/
private noncomputable abbrev c_lower_word3 : ℝ := 2 - √5

/-- c_lower_word2 = (1 - √5)/2 by definition of goldenConj -/
lemma c_lower_word2_eq : c_lower_word2 = (1 - √5) / 2 := by
  unfold c_lower_word2 Real.goldenConj; rfl

/-- (1 - sqrt(5))/2 > -1 since sqrt(5) < 3 -/
lemma c_lower_word2_gt_neg1 : c_lower_word2 > -1 := by
  rw [c_lower_word2_eq]
  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [sqrt5_sq]
  linarith

/-- c_upper_word2 = c_lower_word3 (the intervals are adjacent) -/
lemma c_upper_word2_eq_c_lower_word3 : c_upper_word2 = c_lower_word3 := rfl

/-- (1 - sqrt(5))/2 < 2 - sqrt(5) -/
lemma c_lower_lt_upper_word2 : c_lower_word2 < c_upper_word2 := by
  rw [c_lower_word2_eq]
  unfold c_upper_word2
  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [sqrt5_sq]
  linarith

/-- For x in [length1, length1 + length2), we have c = 2x - 1 >= (1-sqrt(5))/2. -/
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

/-- For x < length1 + length2, we have c = 2x - 1 < 2 - sqrt(5). -/
lemma interval1_c_upper_bound (x : ℝ) (hx : x < length1 + length2) :
    2 * x - 1 < 2 - √5 := by
  have h_length12 : length1 + length2 = (3 - √5) / 2 := length12_eq_sqrt5
  calc 2 * x - 1 < 2 * (length1 + length2) - 1 := by linarith
    _ = 2 * ((3 - √5) / 2) - 1 := by rw [h_length12]
    _ = 3 - √5 - 1 := by ring
    _ = 2 - √5 := by ring

/-! ## z1 cross-disk bound

For word2, z1 = -1 + zeta5 * (z0 + 1) where z0 = c * E.
z1 - 1 = -2 + zeta5 + c * (1 - zeta5^4)
conj(z1 - 1) = -2 + zeta5^4 + c * (1 - zeta5) = (zeta5^4 - 2) + c * (1 - zeta5)

This is the same expression as for word3 z1, but with a different c range.
-/

set_option maxHeartbeats 600000 in
/-- z1 bound for word2: ||(zeta5^4 - 2) + c*(1 - zeta5)|| <= r_crit for c in [(1-sqrt5)/2, 2-sqrt5]

The proof uses quadratic analysis. The parabola opens upward with vertex at (3-sqrt5)/4 > 0,
which is above the interval [(1-sqrt5)/2, 2-sqrt5] = [-0.618, -0.236].
So f is decreasing on the interval, and maximum is at the lower endpoint c = (1-sqrt5)/2. -/
lemma cross_disk_w2_z1_bound (c : ℝ) (hc_lo : (1 - √5) / 2 ≤ c) (hc_hi : c ≤ 2 - √5) :
    ‖(ζ₅^4 - 2 : ℂ) + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  -- The proof follows the same pattern as cross_disk_w3_z1_bound.
  -- At c = 2 - sqrt(5) (upper bound), we can use normSq_w3_z1_at_lower.
  -- At c = (1 - sqrt(5))/2 (lower bound), we verify the bound directly.
  -- Since f is decreasing on the interval (vertex above), max is at lower endpoint.
  set A : ℂ := ζ₅^4 - 2 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ TDCSG.Definitions.φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  -- At upper endpoint (c = 2 - sqrt5), use word3's bound
  have h_at_upper : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]
    have h_expr : (ζ₅^4 - 2 : ℂ) + ((2 - √5 : ℝ) : ℂ) * (1 - ζ₅) = ζ₅^4 - (2 - √5)*ζ₅ - √5 := by
      push_cast; ring
    rw [h_expr]
    exact normSq_w3_z1_at_lower

  -- At lower endpoint, verify bound directly (key calculation)
  have h_at_lower : ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]
    -- The expression simplifies to zeta5^4 - ((1-sqrt5)/2)*zeta5 - (3+sqrt5)/2
    -- ||...||^2 = (13 - 5*sqrt5)/2 <= (7 + sqrt5)/2 = 3 + phi
    -- since 13 - 5*sqrt5 <= 7 + sqrt5 iff 6 <= 6*sqrt5 iff 1 <= sqrt5, true
    have h_expr : (ζ₅^4 - 2 : ℂ) + (((1 - √5)/2 : ℝ) : ℂ) * (1 - ζ₅) =
        ζ₅^4 - ((1 - √5)/2 : ℝ) * ζ₅ - ↑((3 + √5) / 2 : ℝ) := by
      push_cast; ring
    rw [h_expr]
    -- Compute normSq
    rw [Complex.normSq_apply]
    -- Re part: (sqrt5-1)/4 - ((1-sqrt5)/2)*((sqrt5-1)/4) - (3+sqrt5)/2
    --        = (sqrt5-1)/4 * (1 - (1-sqrt5)/2) - (3+sqrt5)/2
    --        = (sqrt5-1)/4 * ((2 - 1 + sqrt5)/2) - (3+sqrt5)/2
    --        = (sqrt5-1)/4 * ((1+sqrt5)/2) - (3+sqrt5)/2
    --        = (sqrt5-1)*(1+sqrt5)/8 - (3+sqrt5)/2
    --        = (5-1)/8 - (3+sqrt5)/2 = 1/2 - (3+sqrt5)/2 = -(2+sqrt5)/2 = (-2-sqrt5)/2
    -- Actually let me recalculate more carefully...
    -- Re(zeta5^4) = (sqrt5-1)/4
    -- Re(((1-sqrt5)/2)*zeta5) = ((1-sqrt5)/2) * Re(zeta5) = ((1-sqrt5)/2) * ((sqrt5-1)/4)
    --                        = -(sqrt5-1)^2/8 = -(6-2*sqrt5)/8 = (sqrt5-3)/4
    -- Re((3+sqrt5)/2) = (3+sqrt5)/2
    -- Total: (sqrt5-1)/4 - (sqrt5-3)/4 - (3+sqrt5)/2
    --      = ((sqrt5-1) - (sqrt5-3))/4 - (3+sqrt5)/2 = 2/4 - (3+sqrt5)/2 = 1/2 - (3+sqrt5)/2
    --      = (1 - 3 - sqrt5)/2 = (-2 - sqrt5)/2
    have h_re : (ζ₅^4 - ((1 - √5)/2 : ℝ) * ζ₅ - ↑((3 + √5) / 2 : ℝ) : ℂ).re = (-2 - √5) / 2 := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_pow4_re, zeta5_re, zeta5_im_eq_sin]
      ring_nf
      nlinarith [sqrt5_sq]
    -- Im part: Im(zeta5^4) = -sin(2*pi/5)
    -- Im(((1-sqrt5)/2)*zeta5) = ((1-sqrt5)/2) * sin(2*pi/5)
    -- Total: -sin(2*pi/5) - ((1-sqrt5)/2)*sin(2*pi/5) = sin(2*pi/5) * (-1 - (1-sqrt5)/2)
    --      = sin(2*pi/5) * ((-2 - 1 + sqrt5)/2) = sin(2*pi/5) * ((sqrt5-3)/2)
    have h_im : (ζ₅^4 - ((1 - √5)/2 : ℝ) * ζ₅ - ↑((3 + √5) / 2 : ℝ) : ℂ).im =
        Real.sin (2 * π / 5) * ((√5 - 3) / 2) := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_pow4_im', zeta5_im_eq_sin]
      ring
    rw [h_re, h_im]
    have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
    simp only [← sq]
    -- ((-2-sqrt5)/2)^2 + (sin(2pi/5) * ((sqrt5-3)/2))^2
    -- = ((2+sqrt5)/2)^2 + sin^2(2pi/5) * ((sqrt5-3)/2)^2
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
      _ = 3 + φ := by unfold φ TDCSG.Definitions.φ Real.goldenRatio; ring
      _ ≤ 3 + φ := le_refl _

  -- Quadratic coefficients
  have h_coeff_a : Complex.normSq B = (5 - √5) / 2 := by rw [hB_def]; exact normSq_B4
  have h_coeff_b : (A * starRingEnd ℂ B).re = (2*√5 - 5) / 2 := by
    rw [hA_def, hB_def]; exact re_A_w3_z1_mul_conj_B
  have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]
  have h_vertex : -(((2*√5 - 5) / 2) / ((5 - √5) / 2)) = (3 - √5) / 4 := w3_z1_vertex

  -- Vertex is above the interval (both endpoints are negative, vertex is positive)
  have h_sqrt5_gt_2 : √5 > 2 := by
    have : (2 : ℝ)^2 < 5 := by norm_num
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).mpr this
  have h_vertex_above : (3 - √5) / 4 > 2 - √5 := by nlinarith [sqrt5_sq, h_sqrt5_gt_2]

  -- f is decreasing on interval since vertex > upper bound and a > 0
  -- So max is at lower endpoint
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
    -- f(c2) - f(c1) = (c2 - c1) * (2*Re(A*conj(B)) + (c1+c2)*||B||^2)
    -- Since c1 + c2 <= 2*(2-sqrt5) and vertex = -(Re(A*conj(B)))/(||B||^2) = (3-sqrt5)/4 > 0
    -- We need: 2*Re(A*conj(B)) + (c1+c2)*||B||^2 <= 0
    have h_sum_bound : c₁ + c₂ ≤ 2 * (2 - √5) := by linarith
    -- At c1 + c2 = 2*(2-sqrt5), we have:
    -- 2*(2*sqrt5-5)/2 + 2*(2-sqrt5)*(5-sqrt5)/2
    -- = (2*sqrt5-5) + (2-sqrt5)*(5-sqrt5)
    -- = (2*sqrt5-5) + (10 - 2*sqrt5 - 5*sqrt5 + 5)
    -- = (2*sqrt5-5) + (15 - 7*sqrt5)
    -- = 10 - 5*sqrt5 = 5*(2-sqrt5) < 0 since sqrt5 > 2
    have h_factor_neg_at_bound : 2 * ((2*√5 - 5) / 2) + 2 * (2 - √5) * ((5 - √5) / 2) ≤ 0 := by
      have h1 : 2 * ((2*√5 - 5) / 2) = 2*√5 - 5 := by ring
      have h2 : 2 * (2 - √5) * ((5 - √5) / 2) = (2 - √5) * (5 - √5) := by ring
      have h3 : (2 - √5) * (5 - √5) = 15 - 7*√5 := by nlinarith [sqrt5_sq]
      rw [h1, h2, h3]
      -- 2*sqrt5 - 5 + 15 - 7*sqrt5 = 10 - 5*sqrt5 = 5*(2 - sqrt5) < 0
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
    -- f(c2) - f(c1) = (c2 - c1) * factor, factor <= 0, c2 >= c1
    -- So f(c2) - f(c1) <= 0, i.e., f(c2) <= f(c1)
    -- Rewrite in terms of coefficient values to help ring
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
    -- Need normSq A = 6 - √5
    have h_normSq_A : Complex.normSq A = 6 - √5 := by rw [hA_def]; exact normSq_A_w3_z1
    rw [h_normSq_A]
    linarith [h_diff, h_prod_nonpos]

  rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]

  calc Complex.normSq ((ζ₅^4 - 2) + (c : ℂ) * (1 - ζ₅))
      ≤ Complex.normSq ((ζ₅^4 - 2) + (((1 - √5)/2 : ℝ) : ℂ) * (1 - ζ₅)) := by
        apply h_mono ((1 - √5)/2) c (le_refl _) hc_lo hc_hi
    _ ≤ 3 + φ := by rw [← hA_def, ← hB_def, Complex.normSq_eq_norm_sq]; exact h_at_lower

/-! ## z2 cross-disk bound

For word2, z2 = 1 + zeta5 * (z1 - 1)
z2 + 1 = 2 - 2*zeta5 + zeta5^2 + c * (zeta5 - 1)
conj(z2 + 1) = 2 - 2*zeta5^4 + zeta5^3 + c * (zeta5^4 - 1)

A = 2 - 2*zeta5^4 + zeta5^3
B = zeta5^4 - 1

This is the same as word3 z2 expressions.
The vertex is at (7-sqrt5)/4 > 1 > interval, so f is decreasing on interval.
Max is at lower endpoint c = (1-sqrt5)/2.
-/

/-- z2 bound for word2: ||(2 - 2*zeta5^4 + zeta5^3) + c*(zeta5^4 - 1)|| <= r_crit
Proof via quadratic analysis with vertex at (7-sqrt5)/4 > 2-sqrt5, so f decreasing on interval. -/
lemma cross_disk_w2_z2_bound (c : ℝ) (hc_lo : (1 - √5) / 2 ≤ c) (hc_hi : c ≤ 2 - √5) :
    ‖((2 : ℂ) - 2*ζ₅^4 + ζ₅^3) + (c : ℂ) * (ζ₅^4 - 1)‖ ≤ r_crit := by
  -- The expression coefficients are the same as word3 z2 with different c range
  -- Vertex at (7-sqrt5)/4 > 1 > 2-sqrt5 > (1-sqrt5)/2 so max at lower endpoint
  set A : ℂ := 2 + ζ₅^3 - 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^4 - 1 with hB_def

  -- Reorder terms to match A
  have h_expr_eq : ∀ t : ℝ, ((2 : ℂ) - 2*ζ₅^4 + ζ₅^3) + (t : ℂ) * (ζ₅^4 - 1) = A + (t : ℂ) * B := by
    intro t; simp only [hA_def, hB_def]; ring

  rw [h_expr_eq, show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ TDCSG.Definitions.φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  -- Quadratic coefficients
  have h_coeff_a : Complex.normSq B = (5 - √5) / 2 := by rw [hB_def]; exact normSq_B3
  have h_coeff_b : (A * starRingEnd ℂ B).re = (3*√5 - 10) / 2 := by
    rw [hA_def, hB_def]; exact re_A_w3_z2_mul_conj_B
  have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]
  have h_vertex : -(((3*√5 - 10) / 2) / ((5 - √5) / 2)) = (7 - √5) / 4 := w3_z2_vertex

  -- Vertex is above the interval (vertex > 1 > 2-√5 > (1-√5)/2)
  -- (7 - √5)/4 > 2 - √5  iff  7 - √5 > 8 - 4√5  iff  3√5 > 1  iff  √5 > 1/3, true since √5 > 2
  have h_sqrt5_gt_1 : √5 > 1 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5)
  have h_vertex_above : (7 - √5) / 4 > 2 - √5 := by nlinarith [h_sqrt5_gt_1]

  -- At upper endpoint c = 2-√5, use w3's bound
  have h_at_upper : ‖A + ((2 - √5 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]
    -- A + (2-√5)*B = (2 + ζ₅³ - 2ζ₅⁴) + (2-√5)*(ζ₅⁴ - 1)
    --             = 2 + ζ₅³ - 2ζ₅⁴ + (2-√5)*ζ₅⁴ - (2-√5)
    --             = √5 + ζ₅³ + (-2 + 2 - √5)*ζ₅⁴ = √5 + ζ₅³ - √5*ζ₅⁴
    have h_match : (2 + ζ₅^3 - 2*ζ₅^4 : ℂ) + ((2 - √5 : ℝ) : ℂ) * (ζ₅^4 - 1) =
        (√5 : ℂ) + ζ₅^3 - (√5 : ℂ) * ζ₅^4 := by push_cast; ring
    rw [h_match]
    exact normSq_w3_z2_at_lower

  -- At lower endpoint c = (1-√5)/2, compute bound directly
  have h_at_lower : ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    rw [hA_def, hB_def, ← Complex.normSq_eq_norm_sq]
    -- A + ((1-√5)/2)*B = (2 + ζ₅³ - 2ζ₅⁴) + ((1-√5)/2)*(ζ₅⁴ - 1)
    --                  = (2 - (1-√5)/2) + ζ₅³ + (-2 + (1-√5)/2)*ζ₅⁴
    --                  = (3+√5)/2 + ζ₅³ - ((3+√5)/2)*ζ₅⁴
    have h_expr : (2 + ζ₅^3 - 2*ζ₅^4 : ℂ) + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1) =
        ↑((3 + √5)/2 : ℝ) + ζ₅^3 - ↑((3 + √5)/2 : ℝ) * ζ₅^4 := by push_cast; ring
    rw [h_expr, Complex.normSq_apply]
    -- Re part: (3+√5)/2 + Re(ζ₅³) - ((3+√5)/2)*Re(ζ₅⁴)
    --        = (3+√5)/2 + (1-√5)/4 - ((3+√5)/2)*((√5-1)/4)
    have h_re : ((↑((3 + √5)/2 : ℝ) + ζ₅^3 - ↑((3 + √5)/2 : ℝ) * ζ₅^4) : ℂ).re =
        (3 + √5) / 2 + (-(√5 + 1) / 4) - ((3 + √5) / 2) * ((√5 - 1) / 4) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_cubed_re, zeta5_pow4_re]
      ring
    -- Im part: Im(ζ₅³) - ((3+√5)/2)*Im(ζ₅⁴)
    --        = -sin(π/5) - ((3+√5)/2)*(-sin(2π/5))
    --        = -sin(π/5) + ((3+√5)/2)*sin(2π/5)
    -- Using sin(2π/5) = sin(π/5)*(1+√5)/2, this equals sin(π/5)*(1+√5)
    have h_im : ((↑((3 + √5)/2 : ℝ) + ζ₅^3 - ↑((3 + √5)/2 : ℝ) * ζ₅^4) : ℂ).im =
        Real.sin (π / 5) * (1 + √5) := by
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [zeta5_cubed_im', zeta5_pow4_im']
      have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
        rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul, Real.cos_pi_div_five]
        ring
      rw [h_sin_double]
      -- Goal: -sin(π/5) + (3+√5)/2 * (sin(π/5)*(1+√5)/2) = sin(π/5)*(1+√5)
      -- = sin(π/5)*(-1 + (3+√5)*(1+√5)/4) = sin(π/5)*(1+√5)
      -- (3+√5)*(1+√5) = 8 + 4√5, so -1 + (8+4√5)/4 = 1 + √5 ✓
      have h_prod : (3 + √5) * (1 + √5) = 8 + 4*√5 := by nlinarith [sqrt5_sq]
      have h_factor : -1 + (3 + √5) * (1 + √5) / 4 = 1 + √5 := by
        rw [h_prod]; ring
      -- Transform goal: LHS = sin(π/5)*(-1 + (3+√5)*(1+√5)/4)
      have h_goal : 0 + -Real.sin (π / 5) - ((3 + √5) / 2 * -(Real.sin (π / 5) * (1 + √5) / 2) + 0 * (ζ₅^4).re) =
          Real.sin (π / 5) * (-1 + (3 + √5) * (1 + √5) / 4) := by ring
      rw [h_goal, h_factor]
    rw [h_re, h_im]
    -- Re = (3+√5)/2 - (√5+1)/4 - ((3+√5)/2)*((√5-1)/4)
    --    = (3+√5)/2 - (√5+1)/4 - (√5+1)/4 = (3+√5)/2 - (√5+1)/2 = 1
    have h_re_val : (3 + √5) / 2 + (-(√5 + 1) / 4) - ((3 + √5) / 2) * ((√5 - 1) / 4) = 1 := by
      nlinarith [sqrt5_sq]
    -- ||...||^2 = 1 + sin²(π/5)*(1+√5)² = 1 + ((5-√5)/8)*(6+2√5) = 1 + (5+√5)/2 = (7+√5)/2 = 3+φ
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
      _ = 3 + φ := by unfold φ TDCSG.Definitions.φ Real.goldenRatio; ring
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

  -- Function is decreasing since vertex > all c in interval and a > 0
  have h_mono : ∀ c₁ c₂ : ℝ, (1 - √5) / 2 ≤ c₁ → c₁ ≤ c₂ → c₂ ≤ 2 - √5 →
      Complex.normSq (A + (c₂ : ℂ) * B) ≤ Complex.normSq (A + (c₁ : ℂ) * B) := by
    intro c₁ c₂ hc1_lo hc12 hc2_hi
    rw [h_normSq_expand c₁, h_normSq_expand c₂, h_coeff_a, h_coeff_b, h_normSq_A]
    -- f(c2) - f(c1) = (c2 - c1) * (2*b + (c1+c2)*a)
    -- Since vertex = -b/a = (7-√5)/4 > 2-√5 ≥ c1+c2)/2, we have c1+c2 < (7-√5)/2
    -- Need: 2*b + (c1+c2)*a ≤ 0, i.e., (3√5-10) + (c1+c2)*(5-√5)/2 ≤ 0
    have h_sum_bound : c₁ + c₂ ≤ 2 * (2 - √5) := by linarith
    -- At max sum: (3√5-10) + 2*(2-√5)*(5-√5)/2 = (3√5-10) + (2-√5)*(5-√5)
    -- = (3√5-10) + (10 - 2√5 - 5√5 + 5) = (3√5-10) + (15 - 7√5) = 5 - 4√5 < 0
    have h_factor_neg_at_bound : 2 * ((3*√5 - 10) / 2) + 2 * (2 - √5) * ((5 - √5) / 2) ≤ 0 := by
      have h0 : 2 * ((3*√5 - 10) / 2) = 3*√5 - 10 := by ring
      have h1 : 2 * (2 - √5) * ((5 - √5) / 2) = (2 - √5) * (5 - √5) := by ring
      have h2 : (2 - √5) * (5 - √5) = 15 - 7*√5 := by nlinarith [sqrt5_sq]
      rw [h0, h1, h2]
      -- (3√5 - 10) + (15 - 7√5) = 5 - 4√5 = 5 - 4*2.236... ≈ -3.9 < 0
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

/-! ## z3 cross-disk bound

For word2, z3 = -1 + zeta5 * (z2 + 1)
z3 - 1 = -2 + 2*zeta5 - 2*zeta5^2 + zeta5^3 + c * (zeta5^2 - zeta5)
conj(z3 - 1) = -2 + 2*zeta5^4 - 2*zeta5^3 + zeta5^2 + c * (zeta5^3 - zeta5^4)

A = -2 + 2*zeta5^4 - 2*zeta5^3 + zeta5^2
B = zeta5^3 - zeta5^4

The vertex is at (5-3*sqrt5)/4 which is less than (1-sqrt5)/2.
So f is increasing on the interval, max at upper endpoint c = 2-sqrt5.
At c = 2-sqrt5, the expression equals word3's z3 at its lower bound.
-/

/-- z3 bound for word2: ||(−2 + 2*zeta5^4 − 2*zeta5^3 + zeta5^2) + c*(zeta5^3 − zeta5^4)|| <= r_crit
Proof via quadratic analysis. Vertex at (5-3*sqrt5)/4 is inside the interval, parabola opens upward.
Both endpoints are equidistant from vertex, giving equal maximum values.
At c = 2-sqrt5 (upper), expression matches word3's z3 at lower bound. -/
lemma cross_disk_w2_z3_bound (c : ℝ) (hc_lo : (1 - √5) / 2 ≤ c) (hc_hi : c ≤ 2 - √5) :
    ‖((-2 : ℂ) + 2*ζ₅^4 - 2*ζ₅^3 + ζ₅^2) + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by
  -- The expression is the same as word3 z3: A = -2 + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4, B = ζ₅^3 - ζ₅^4
  set A : ℂ := -2 + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4 with hA_def
  set B : ℂ := ζ₅^3 - ζ₅^4 with hB_def

  -- Rewrite expression to match A, B (just reordering terms)
  have h_expr_eq : ∀ t : ℝ, ((-2 : ℂ) + 2*ζ₅^4 - 2*ζ₅^3 + ζ₅^2) + (t : ℂ) * (ζ₅^3 - ζ₅^4) =
      A + (t : ℂ) * B := by intro t; simp only [hA_def, hB_def]; ring

  rw [h_expr_eq, show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ TDCSG.Definitions.φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos), ← Complex.normSq_eq_norm_sq]

  -- At upper endpoint c = 2 - sqrt5, use w3_z3_at_lower
  have h_at_upper : Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) ≤ 3 + φ := by
    -- Direct calculation shows A + (2-√5)*B = -2 + ζ₅^2 - √5*ζ₅^3 + √5*ζ₅^4
    have h_w3 := w3_z3_at_lower_expr
    -- w3_z3_at_lower_expr shows the w3 expression at c = 2-√5
    have h_match : A + ((2 - √5 : ℝ) : ℂ) * B = (-2 : ℂ) + ζ₅^2 - (√5 : ℂ) * ζ₅^3 + (√5 : ℂ) * ζ₅^4 := by
      simp only [hA_def, hB_def]; push_cast; ring
    rw [h_match]
    exact normSq_w3_z3_at_lower

  -- Quadratic coefficients are same as w3_z3
  have h_coeff_a : Complex.normSq B = (5 - √5) / 2 := by rw [hB_def]; exact normSq_B
  have h_coeff_b : (A * starRingEnd ℂ B).re = (5*√5 - 10) / 2 := by
    rw [hA_def, hB_def]; exact re_A_w3_z3_mul_conj_B

  have h_a_pos : (5 - √5) / 2 > 0 := by nlinarith [sqrt5_sq]

  -- Vertex at (5-3*sqrt5)/4 is INSIDE the interval [(1-√5)/2, 2-√5]
  -- Both endpoints are equidistant from vertex: distance = (3-√5)/4
  -- Since parabola opens upward, max is at endpoints (which give equal values)

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

  -- Show f(c) ≤ f(2-√5) for all c in interval via quadratic analysis
  -- f(c) = A_0 + 2*b*c + a*c^2 where a > 0, vertex at -b/a = (5-3√5)/4
  -- Since vertex in interval and both endpoints equidistant, f(c) ≤ f(endpoint)
  have h_normSq_A : Complex.normSq A = 16 - 7*√5 := by rw [hA_def]; exact normSq_A_w3_z3

  -- f(c) ≤ max(f(lower), f(upper))
  -- Since endpoints equidistant from vertex: f(lower) = f(upper)
  have h_endpoints_equal : Complex.normSq (A + (((1 - √5)/2 : ℝ) : ℂ) * B) =
      Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) := by
    rw [h_normSq_expand ((1-√5)/2), h_normSq_expand (2-√5), h_coeff_a, h_coeff_b, h_normSq_A]
    -- f(c) = (16 - 7√5) + 2c*(5√5-10)/2 + c²*(5-√5)/2
    --      = (16 - 7√5) + c*(5√5-10) + c²*(5-√5)/2
    -- At lower: c = (1-√5)/2, c² = (6-2√5)/4 = (3-√5)/2
    -- At upper: c = 2-√5, c² = (2-√5)² = 9 - 4√5
    have h_c_lo_sq : ((1 - √5) / 2)^2 = (3 - √5) / 2 := by nlinarith [sqrt5_sq]
    have h_c_hi_sq : (2 - √5)^2 = 9 - 4*√5 := by nlinarith [sqrt5_sq]
    rw [h_c_lo_sq, h_c_hi_sq]
    ring_nf
    nlinarith [sqrt5_sq]

  -- For any c in [lower, upper], f(c) ≤ f(upper) since vertex in interior
  -- and f is convex (a > 0), max at endpoints which are equal
  have h_bound : ∀ c' : ℝ, (1 - √5) / 2 ≤ c' → c' ≤ 2 - √5 →
      Complex.normSq (A + (c' : ℂ) * B) ≤ Complex.normSq (A + ((2 - √5 : ℝ) : ℂ) * B) := by
    intro c' hc'_lo hc'_hi
    rw [h_normSq_expand c', h_normSq_expand (2-√5), h_coeff_a, h_coeff_b, h_normSq_A]
    -- Convex quadratic: f(c) ≤ max(f(endpoints))
    -- vertex = (5-3√5)/4 ≈ -0.427, interval ≈ [-0.618, -0.236]
    -- Since endpoints give equal values and f is convex, f(c) ≤ f(endpoints) for c in interval
    have h_c_hi_sq : (2 - √5)^2 = 9 - 4*√5 := by nlinarith [sqrt5_sq]
    rw [h_c_hi_sq]
    -- f(c') - f(2-√5) = (c' - (2-√5)) * ((5√5-10) + (c' + 2 - √5) * (5-√5)/2)
    -- Need to show this is ≤ 0
    have h_sqrt5_cubed : √5^3 = 5 * √5 := by
      have h1 : √5^3 = √5^2 * √5 := by ring
      rw [h1, sqrt5_sq]
    have h_diff_formula : (16 - 7*√5) + 2 * c' * ((5*√5 - 10) / 2) + c'^2 * ((5 - √5) / 2) -
        ((16 - 7*√5) + 2 * (2 - √5) * ((5*√5 - 10) / 2) + (9 - 4*√5) * ((5 - √5) / 2)) =
        (c' - (2 - √5)) * ((5*√5 - 10) + (c' + 2 - √5) * ((5 - √5) / 2)) := by
      ring_nf
      nlinarith [sqrt5_sq, h_sqrt5_cubed]
    -- c' - (2-√5) ≤ 0 since c' ≤ 2-√5
    have h_first_factor : c' - (2 - √5) ≤ 0 := by linarith
    -- Second factor: (5√5-10) + (c' + 2 - √5)*(5-√5)/2
    -- At c' = (1-√5)/2: sum = (1-√5)/2 + 2 - √5 = (1-√5 + 4 - 2√5)/2 = (5-3√5)/2
    -- Factor = (5√5-10) + (5-3√5)/2 * (5-√5)/2
    -- = (5√5-10) + (25 - 5√5 - 15√5 + 3*5)/(4) = (5√5-10) + (40 - 20√5)/4
    -- = (5√5-10) + (10 - 5√5) = 0
    -- So at lower bound, factor = 0. For c' > lower, sum increases, factor > 0
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
