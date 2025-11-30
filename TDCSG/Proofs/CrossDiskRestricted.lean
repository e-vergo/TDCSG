/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.CrossDiskBasic

/-!
# Cross-Disk Membership Bounds for GG(5,5) - Restricted Parameter Range

This file provides the geometric bounds for the restricted parameter range c ∈ [-1, (1-√5)/2],
which corresponds to the intervals needed for word1 and word2 applications.

## Main Results

- `cross_disk_z2_bound_restricted`: For c in [-1, (1-√5)/2], the norm bound holds for z2
- `cross_disk_z3_bound_restricted`: For c in [-1, (1-√5)/2], the norm bound holds for z3
- `cross_disk_z4_bound_restricted`: For c in [-1, (1-√5)/2], the norm bound holds for z4

## Key Insight

The word1/word2 lemmas require x in [0, length1) where length1 = 1/(2*(1+φ)).
This constrains c = 2x - 1 to [-1, (1-√5)/2), a much smaller range than [-1, 1].

For this restricted range, the quadratic functions f(c) = ||A + cB||² achieve their maxima
at specific endpoints, allowing us to verify bounds precisely.
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real TDCSG.Definitions

/-! ### z2 cross-disk bound

For any c with -1 <= c <= (1-sqrt5)/2, the expression is bounded.

The key insight is that the quadratic f(c) = ||A + cB||^2 has positive leading coefficient,
so on any interval [a, b], the maximum is at one of the endpoints.
Since (1-sqrt5)/2 < 0 and the vertex of the parabola is positive (as we'll show),
the maximum on [-1, (1-sqrt5)/2] is at c = -1.
-/
lemma cross_disk_z2_bound_restricted (c : ℝ) (hc_lo : -1 ≤ c) (hc_hi : c ≤ (1 - √5) / 2) :
    ‖(-2 : ℂ) + ζ₅^2 + (c : ℂ) * (ζ₅^3 - ζ₅^4)‖ ≤ r_crit := by
  set A : ℂ := -2 + ζ₅^2 with hA_def
  set B : ℂ := ζ₅^3 - ζ₅^4 with hB_def

  have hB_ne : B ≠ 0 := by rw [hB_def]; exact zeta5_cubed_minus_fourth_ne_zero

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
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

      have h_vertex_lt_c : -(3 * √5 / 2) / ((5 - √5) / 2) < c := by
        calc -(3 * √5 / 2) / ((5 - √5) / 2) < -1 := h_vertex
          _ ≤ c := hc_lo

      have h_sum_gt_2vertex : c + c_upper > 2 * (-(3 * √5 / 2) / ((5 - √5) / 2)) := by
        have hv : -(3 * √5 / 2) / ((5 - √5) / 2) < -1 := h_vertex
        have h_upper_gt_vertex : c_upper > -(3 * √5 / 2) / ((5 - √5) / 2) := by
          have h_upper_val : c_upper = (1 - √5) / 2 := rfl
          calc -(3 * √5 / 2) / ((5 - √5) / 2) < -1 := h_vertex
            _ < (1 - √5) / 2 := by nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
        linarith

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

  calc ‖A + (c : ℂ) * B‖^2 ≤ ‖A + (((1 - √5)/2) : ℂ) * B‖^2 := h_mono
    _ = 3 + φ := h_f_at_upper_eq

/-! ### z3 cross-disk bound lemmas -/

/-- Re(ζ₅⁴ - 1) = (√5 - 5)/4 -/
lemma B3_re : (ζ₅^4 - 1 : ℂ).re = (√5 - 5) / 4 := by
  simp only [Complex.sub_re, Complex.one_re]
  rw [zeta5_pow4_re]
  ring

/-- Im(ζ₅⁴ - 1) = -sin(2π/5) -/
lemma B3_im : (ζ₅^4 - 1 : ℂ).im = -Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im, Complex.one_im]
  rw [zeta5_pow4_im_neg, zeta5_im_eq_sin]
  ring

/-- ||B3||² = (ζ₅⁴ - 1).normSq = (5 - √5)/2 -/
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
    calc Real.sin (2 * π / 5)^2 = 1 - Real.cos (2 * π / 5)^2 := h1
      _ = 1 - ((√5 - 1) / 4)^2 := by rw [h_cos]
      _ = 1 - (√5^2 - 2*√5 + 1) / 16 := by ring
      _ = 1 - (5 - 2*√5 + 1) / 16 := by simp only [sqrt5_sq]
      _ = (5 + √5) / 8 := by ring
  calc ((√5 - 5) / 4)^2 + (-Real.sin (2 * π / 5))^2
      = (√5 - 5)^2 / 16 + Real.sin (2 * π / 5)^2 := by ring
    _ = (√5^2 - 10*√5 + 25) / 16 + (5 + √5) / 8 := by rw [h_sin_sq]; ring
    _ = (5 - 10*√5 + 25) / 16 + (5 + √5) / 8 := by simp only [sqrt5_sq]
    _ = (5 - √5) / 2 := by ring

/-- sin²(2π/5) = (5 + √5)/8 -/
lemma sin_sq_two_pi_div_5 : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := by
  have h_cos : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
    rw [cos_two_pi_fifth]
    unfold Real.goldenRatio
    ring
  have h := Real.sin_sq_add_cos_sq (2 * π / 5)
  have h1 : Real.sin (2 * π / 5)^2 = 1 - Real.cos (2 * π / 5)^2 := by linarith
  calc Real.sin (2 * π / 5)^2 = 1 - Real.cos (2 * π / 5)^2 := h1
    _ = 1 - ((√5 - 1) / 4)^2 := by rw [h_cos]
    _ = 1 - (√5^2 - 2*√5 + 1) / 16 := by ring
    _ = 1 - (5 - 2*√5 + 1) / 16 := by simp only [sqrt5_sq]
    _ = (5 + √5) / 8 := by ring

/-- normSq at c = (1-√5)/2 for z3

At c = (1-√5)/2:
Expression = (2 - 2ζ₅ + ζ₅³) + ((1-√5)/2)(ζ₅⁴ - 1)

Re = 2 - 2*(√5-1)/4 - (√5+1)/4 + (1-√5)/2*((√5-5)/4)
   = 2 - (√5-1)/2 - (√5+1)/4 + (1-√5)(√5-5)/8
   = 2 - (2√5-2+√5+1)/4 + (6√5-10)/8
   = 2 - (3√5-1)/4 + (3√5-5)/4
   = 2 + (-4)/4 = 1

Im = -2*sin(2π/5) - sin(π/5) + (1-√5)/2*(-sin(2π/5))
   = -sin(2π/5)*(2 + (1-√5)/2) - sin(π/5)
   = -sin(2π/5)*(5-√5)/2 - sin(π/5)
-/
lemma z3_normSq_at_c_upper :
    Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1)) = (7 + √5) / 2 := by
  rw [Complex.normSq_apply]
  simp only [← sq]

  -- Real part = 1
  have h_re : ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (((1 - √5)/2 : ℝ) : ℂ) * (ζ₅^4 - 1)).re = 1 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               Complex.one_re, Complex.sub_im, Complex.one_im]
    have h2re : (2 : ℂ).re = 2 := by rfl
    have h2im : (2 : ℂ).im = 0 := by rfl
    rw [h2re, h2im]
    simp only [zero_mul, sub_zero]
    rw [zeta5_re, zeta5_cubed_re, zeta5_pow4_re]
    -- Goal: 2 - 2 * ((√5 - 1) / 4) + -(√5 + 1) / 4 + (1 - √5) / 2 * ((√5 - 1) / 4 - 1) = 1
    have h3 : (1 - √5) * (√5 - 5) = 6*√5 - 10 := by nlinarith [sqrt5_sq]
    nlinarith [sqrt5_sq, h3]

  -- Imaginary part = -sin(2π/5)*(5-√5)/2 - sin(π/5)
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
  -- Now compute 1² + (sin(2π/5)*(5-√5)/2 + sin(π/5))²
  -- Using sin(2π/5) = 2*sin(π/5)*cos(π/5) = 2*sin(π/5)*(1+√5)/4 = sin(π/5)*(1+√5)/2
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  have h_sin_pi5_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- sin(2π/5)*(5-√5)/2 = sin(π/5)*(1+√5)/2*(5-√5)/2 = sin(π/5)*(1+√5)(5-√5)/4
  --                    = sin(π/5)*(5-√5+5√5-5)/4 = sin(π/5)*(4√5)/4 = sin(π/5)*√5
  have h_product : Real.sin (2 * π / 5) * (5 - √5) / 2 = Real.sin (π / 5) * √5 := by
    rw [h_sin_double]
    have h1 : (1 + √5) * (5 - √5) = 5 - √5 + 5*√5 - √5^2 := by ring
    have h2 : (1 + √5) * (5 - √5) = 4 * √5 := by nlinarith [sqrt5_sq, h1]
    have h3 : Real.sin (π / 5) * (1 + √5) * (5 - √5) = Real.sin (π / 5) * (4 * √5) := by
      calc Real.sin (π / 5) * (1 + √5) * (5 - √5)
          = Real.sin (π / 5) * ((1 + √5) * (5 - √5)) := by ring
        _ = Real.sin (π / 5) * (4 * √5) := by rw [h2]
    calc Real.sin (π / 5) * (1 + √5) / 2 * (5 - √5) / 2
        = Real.sin (π / 5) * (1 + √5) * (5 - √5) / 4 := by ring
      _ = Real.sin (π / 5) * (4 * √5) / 4 := by rw [h3]
      _ = Real.sin (π / 5) * √5 := by ring

  -- So Im = -sin(π/5)*√5 - sin(π/5) = -sin(π/5)*(√5 + 1)
  have h_im_simp : -Real.sin (2 * π / 5) * (5 - √5) / 2 - Real.sin (π / 5) =
                   -Real.sin (π / 5) * (√5 + 1) := by
    have h := h_product
    linarith

  calc (1 : ℝ)^2 + (-Real.sin (2 * π / 5) * (5 - √5) / 2 - Real.sin (π / 5))^2
      = 1 + (-Real.sin (π / 5) * (√5 + 1))^2 := by rw [h_im_simp]; ring
    _ = 1 + Real.sin (π / 5)^2 * (√5 + 1)^2 := by ring
    _ = 1 + ((5 - √5) / 8) * (√5 + 1)^2 := by rw [h_sin_pi5_sq]
    _ = 1 + ((5 - √5) / 8) * (√5^2 + 2*√5 + 1) := by ring
    _ = 1 + ((5 - √5) / 8) * (6 + 2*√5) := by nlinarith [sqrt5_sq]
    _ = 1 + (5 - √5) * (6 + 2*√5) / 8 := by ring
    _ = 1 + (20 + 4*√5) / 8 := by nlinarith [sqrt5_sq]
    _ = 1 + (5 + √5) / 2 := by ring
    _ = (7 + √5) / 2 := by ring

/-- (7 + √5)/2 = 3 + φ -/
lemma seven_plus_sqrt5_div_2_eq : (7 + √5) / 2 = 3 + φ := by
  unfold φ Real.goldenRatio
  ring

/-- For c in [-1, (1-√5)/2], the z3 norm is bounded.

The quadratic f(c) = ||A + cB||² has vertex at c_v = (1-3√5)/4 < -1.
Since parabola opens upward and vertex < -1 < (1-√5)/2,
f is increasing on [-1, (1-√5)/2], so max is at c = (1-√5)/2.

At c = (1-√5)/2, we compute ||z3 + 1||² = (7 + √5)/2 = 3 + φ = r_crit².
-/
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
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  -- Vertex is at c_v = (1 - 3√5)/4 < -1
  have h_vertex_lt : (1 - 3*√5) / 4 < -1 := by
    have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
    -- Need √5 > 5/3 to show (1 - 3√5)/4 < -1
    have h_sqrt5_gt : √5 > 5/3 := by
      have h_sq : (5/3 : ℝ)^2 = 25/9 := by norm_num
      have h_lt : (25/9 : ℝ) < 5 := by norm_num
      calc √5 > √(25/9) := Real.sqrt_lt_sqrt (by norm_num) h_lt
        _ = 5/3 := by rw [← h_sq, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5/3)]
    linarith

  -- Since vertex < -1 ≤ c ≤ (1-√5)/2, f is increasing on the interval
  -- So max is at c = (1-√5)/2

  have h_at_c_upper : ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 = 3 + φ := by
    rw [hA_def, hB_def]
    rw [← Complex.normSq_eq_norm_sq]
    rw [z3_normSq_at_c_upper, seven_plus_sqrt5_div_2_eq]

  -- Monotonicity: f(c) ≤ f(c_upper) since f is increasing
  have h_mono : ‖A + (c : ℂ) * B‖^2 ≤ ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 := by
    rw [hA_def, hB_def]
    simp only [← Complex.normSq_eq_norm_sq]

    -- Expand f(t) = ||A + tB||² = ||A||² + 2t*Re(A*conj(B)) + t²*||B||²
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

    -- Compute Re(A*conj(B)) = (4√5 - 5)/2
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

    -- f(c_upper) - f(c) = (c_upper - c) * (derivative at some point between)
    -- Since f is increasing on [vertex, ∞) and both c, c_upper > vertex,
    -- and c ≤ c_upper, we have f(c) ≤ f(c_upper)

    -- More directly: f'(t) = 2*Re(AB*) + 2t*||B||² = (4√5 - 5) + t*(5 - √5)
    -- f'(t) = 0 at t = -(4√5 - 5)/(5 - √5) = (5 - 4√5)/(5 - √5)
    -- Let's verify: (5 - 4√5)(5 + √5)/(25 - 5) = (25 + 5√5 - 20√5 - 20)/20 = (5 - 15√5)/20 = (1 - 3√5)/4

    -- For t > vertex = (1 - 3√5)/4, we have f'(t) > 0
    -- Since c ≥ -1 > (1 - 3√5)/4 ≈ -1.4, f is increasing at c
    -- Similarly for c_upper = (1 - √5)/2 ≈ -0.618 > vertex

    have h_5_minus_sqrt5_pos : 0 < 5 - √5 := by
      have h25 : √25 = 5 := by
        rw [show (25 : ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
      have : √5 < 5 := by
        calc √5 < √25 := Real.sqrt_lt_sqrt (by linarith) (by norm_num)
          _ = 5 := h25
      linarith

    -- The difference f(c_upper) - f(c) ≥ 0 when c ≤ c_upper and f is increasing
    have h_diff_expand : Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3) + 2 * c_upper * ((4*√5 - 5) / 2) +
        c_upper^2 * ((5 - √5) / 2) -
        (Complex.normSq ((2 : ℂ) - 2*ζ₅ + ζ₅^3) + 2 * c * ((4*√5 - 5) / 2) + c^2 * ((5 - √5) / 2)) =
        (c_upper - c) * ((4*√5 - 5) + (c + c_upper) * ((5 - √5) / 2)) := by ring

    -- Need: (4√5 - 5) + (c + c_upper) * ((5 - √5) / 2) ≥ 0 when c, c_upper ≥ -1 and vertex < -1
    -- Since c ≥ -1 and c_upper = (1-√5)/2 ≈ -0.618, we have c + c_upper ≥ -1 + (1-√5)/2 = (1-√5)/2 - 1 = -(1+√5)/2

    have h_c_upper_def : c_upper = (1 - √5) / 2 := rfl
    have h_c_plus_cupper_lo : c + c_upper ≥ -1 + (1 - √5) / 2 := by
      linarith [hc_lo]
    have h_lo_val : -1 + (1 - √5) / 2 = -(1 + √5) / 2 := by ring

    -- At the minimum c + c_upper = -(1+√5)/2:
    -- (4√5 - 5) + (-(1+√5)/2) * ((5 - √5) / 2)
    -- = (4√5 - 5) - (1+√5)(5-√5)/4
    -- = (4√5 - 5) - (5 - √5 + 5√5 - 5)/4
    -- = (4√5 - 5) - (4√5)/4
    -- = (4√5 - 5) - √5
    -- = 3√5 - 5

    -- Since √5 ≈ 2.236, 3√5 ≈ 6.7 > 5, so 3√5 - 5 > 0

    have h_factor_pos : (4*√5 - 5) + (c + c_upper) * ((5 - √5) / 2) ≥ 0 := by
      have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
      have h_sqrt5_gt : √5 > 5 / 3 := by
        have h_sq : (5/3 : ℝ)^2 = 25/9 := by norm_num
        have h_lt : (25/9 : ℝ) < 5 := by norm_num
        calc √5 > √(25/9) := Real.sqrt_lt_sqrt (by norm_num) h_lt
          _ = 5/3 := by rw [← h_sq, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5/3)]
      -- At minimum value of c + c_upper:
      have h_at_min : (4*√5 - 5) + (-(1 + √5) / 2) * ((5 - √5) / 2) = 3*√5 - 5 := by
        nlinarith [sqrt5_sq]
      have h_3sqrt5_gt_5 : 3*√5 > 5 := by linarith [h_sqrt5_gt]
      -- General bound using c + c_upper ≥ -(1+√5)/2
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

    nlinarith [h_factor_pos, h_cupper_minus_c, h_diff_expand]

  calc ‖A + (c : ℂ) * B‖^2 ≤ ‖A + (((1 - √5)/2 : ℝ) : ℂ) * B‖^2 := h_mono
    _ = 3 + φ := h_at_c_upper

/-! ### Helper lemmas for z4 bound -/

/-- Re(1 - zeta5) = (5 - sqrt5)/4 -/
lemma B4_re : (1 - ζ₅ : ℂ).re = (5 - √5) / 4 := by
  simp only [Complex.sub_re, Complex.one_re]
  rw [zeta5_re]
  ring

/-- Im(1 - zeta5) = -sin(2*pi/5) -/
lemma B4_im : (1 - ζ₅ : ℂ).im = -Real.sin (2 * π / 5) := by
  simp only [Complex.sub_im, Complex.one_im]
  rw [zeta5_im_eq_sin]
  ring

/-- ||B4||^2 = (1 - zeta5).normSq = (5 - sqrt5)/2 -/
lemma normSq_B4 : Complex.normSq (1 - ζ₅) = (5 - √5) / 2 := by
  rw [Complex.normSq_apply]
  simp only [← sq]
  rw [B4_re, B4_im]
  have h_sin_sq : Real.sin (2 * π / 5)^2 = (5 + √5) / 8 := sin_sq_two_pi_div_5
  calc ((5 - √5) / 4)^2 + (-Real.sin (2 * π / 5))^2
      = (5 - √5)^2 / 16 + Real.sin (2 * π / 5)^2 := by ring
    _ = (5 - √5)^2 / 16 + (5 + √5) / 8 := by rw [h_sin_sq]
    _ = (25 - 10*√5 + √5^2) / 16 + (5 + √5) / 8 := by ring
    _ = (25 - 10*√5 + 5) / 16 + (5 + √5) / 8 := by simp only [sqrt5_sq]
    _ = (5 - √5) / 2 := by ring

/-- Re(A4) = (-9 + 5√5) / 4 where A4 = -2 + 2ζ₅ - 2ζ₅² + ζ₅⁴ -/
lemma A4_re : ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (-9 + 5*√5) / 4 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  ring

/-- Im(A4) = sin(2π/5) - 2*sin(π/5) where A4 = -2 + 2ζ₅ - 2ζ₅² + ζ₅⁴
    Using: Im(ζ₅) = sin(2π/5), Im(ζ₅²) = sin(π/5), Im(ζ₅⁴) = -sin(2π/5)
    Im(A4) = 2*sin(2π/5) - 2*sin(π/5) - sin(2π/5) = sin(2π/5) - 2*sin(π/5) -/
lemma A4_im : ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4).im = Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im]
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h2re, h2im]
  rw [zeta5_im_eq_sin, zeta5_sq_im', zeta5_pow4_im']
  ring

/-- conj(1 - ζ₅) = 1 - ζ₅⁴ -/
lemma conj_B4 : starRingEnd ℂ (1 - ζ₅) = 1 - ζ₅^4 := by
  rw [map_sub, map_one, zeta5_conj]

/-- Re(A4 * conj(B4)) = (5√5 - 10) / 2 = 5(√5 - 2)/2
    Computed by:
    A4 * conj(B4) = (-2 + 2ζ₅ - 2ζ₅² + ζ₅⁴) * (1 - ζ₅⁴)
    After expanding with ζ₅⁵ = 1: -4 + 3ζ₅⁴ + 4ζ₅ - 2ζ₅² - ζ₅³
    Re = -4 + 3(√5-1)/4 + 4(√5-1)/4 + 2(√5+1)/4 + (√5+1)/4
       = -4 + (3√5 - 3 + 4√5 - 4 + 2√5 + 2 + √5 + 1)/4
       = -4 + (10√5 - 4)/4 = (5√5 - 10)/2 -/
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

/-- Re(-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴) = (-7 + 3√5)/2
    Using: Re(ζ₅) = (√5-1)/4, Re(ζ₅²) = -(√5+1)/4, Re(ζ₅⁴) = (√5-1)/4
    Re = -3 + 3(√5-1)/4 - 2(-(√5+1)/4) + (√5-1)/4
       = -3 + (3√5-3)/4 + (2√5+2)/4 + (√5-1)/4
       = -3 + (6√5-2)/4 = -3 + (3√5-1)/2 = (-7+3√5)/2 -/
lemma A4_at_neg1_re : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).re = (-7 + 3*√5) / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re]
  have h3re : (3 : ℂ).re = 3 := by rfl
  have h3im : (3 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h3re, h3im, h2re, h2im, zero_mul, sub_zero]
  rw [zeta5_re, zeta5_sq_re, zeta5_pow4_re]
  ring

/-- Im(-3 + 3ζ₅ - 2ζ₅² + ζ₅⁴) = 3*sin(2π/5) - 2*sin(π/5) - sin(2π/5) = 2*sin(2π/5) - 2*sin(π/5)
    Using: Im(ζ₅) = sin(2π/5), Im(ζ₅²) = sin(π/5), Im(ζ₅⁴) = -sin(2π/5) -/
lemma A4_at_neg1_im : ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4).im = 2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5) := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im]
  have h3re : (3 : ℂ).re = 3 := by rfl
  have h3im : (3 : ℂ).im = 0 := by rfl
  have h2re : (2 : ℂ).re = 2 := by rfl
  have h2im : (2 : ℂ).im = 0 := by rfl
  simp only [h3re, h3im, h2re, h2im]
  rw [zeta5_im_eq_sin, zeta5_sq_im', zeta5_pow4_im']
  ring

/-- ||−3 + 3ζ₅ − 2ζ₅² + ζ₅⁴||² -/
lemma normSq_A4_at_neg1 : Complex.normSq ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4) =
    ((-7 + 3*√5) / 2)^2 + (2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5))^2 := by
  rw [Complex.normSq_apply, A4_at_neg1_re, A4_at_neg1_im]
  simp only [← sq]

/-- The vertex of f(c) = ||A4 + cB4||² is at c_v = (5 - 3√5)/4.
    c_v > (1-√5)/2 since (5-3√5)/4 > (1-√5)/2 iff (5-3√5)/4 - (2-2√5)/4 = (3-√5)/4 > 0 iff √5 < 3.
    Since our interval is [-1, (1-√5)/2], the vertex is to the right, so f is INCREASING. -/
lemma z4_vertex_gt_c_upper : (5 - 3*√5) / 4 > (1 - √5) / 2 := by
  have h_sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  -- Need √5 < 3
  have h_sqrt5_lt_3 : √5 < 3 := by nlinarith [sqrt5_sq]
  -- (5 - 3√5)/4 - (1 - √5)/2 = (5 - 3√5)/4 - (2 - 2√5)/4 = (3 - √5)/4 > 0
  linarith

/-- ||A4||² = 16 - 7√5 where A4 = -2 + 2ζ₅ - 2ζ₅² + ζ₅⁴.
    Re(A4) = (-9 + 5√5)/4, Im(A4) = sin(π/5)*(√5 - 3)/2
    Re²  = (206 - 90√5)/16 = (103 - 45√5)/8
    Im² = sin²(π/5)*(√5-3)²/4 = ((5-√5)/8)*((14-6√5)/4) = (100-44√5)/32 = (25-11√5)/8
    ||A4||² = (103-45√5 + 25-11√5)/8 = (128-56√5)/8 = 16-7√5 -/
lemma normSq_A4 : Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) = 16 - 7*√5 := by
  rw [Complex.normSq_apply, A4_re, A4_im]
  have h_sin_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  -- sin(2π/5) = sin(π/5) * (1+√5) / 2
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  -- Im(A4) = sin(2π/5) - 2*sin(π/5) = sin(π/5)*((1+√5)/2 - 2) = sin(π/5)*(√5-3)/2
  have h_im_simp : Real.sin (2 * π / 5) - 2 * Real.sin (π / 5) = Real.sin (π / 5) * (√5 - 3) / 2 := by
    rw [h_sin_double]
    ring
  -- Im² = sin²(π/5) * (√5-3)² / 4
  have h_im_sq : (Real.sin (2 * π / 5) - 2 * Real.sin (π / 5))^2 = (25 - 11*√5) / 8 := by
    rw [h_im_simp]
    have h_sq_mul : (Real.sin (π / 5) * (√5 - 3) / 2)^2 = Real.sin (π / 5)^2 * (√5 - 3)^2 / 4 := by ring
    rw [h_sq_mul, h_sin_sq]
    have h_sqrt5_minus_3_sq : (√5 - 3)^2 = 14 - 6*√5 := by nlinarith [sqrt5_sq]
    rw [h_sqrt5_minus_3_sq]
    nlinarith [sqrt5_sq]
  -- Re² = ((-9+5√5)/4)² = (206 - 90√5)/16 = (103 - 45√5)/8
  have h_re_sq : ((-9 + 5*√5) / 4)^2 = (103 - 45*√5) / 8 := by nlinarith [sqrt5_sq]
  simp only [← sq]
  rw [h_re_sq, h_im_sq]
  nlinarith [sqrt5_sq]

/-- (7 - 3√5)/2 ≤ (7 + √5)/2 = 3 + φ -/
lemma seven_minus_3sqrt5_le_three_plus_phi : (7 - 3*√5) / 2 ≤ 3 + φ := by
  have h_sqrt5_nonneg : 0 ≤ √5 := Real.sqrt_nonneg 5
  unfold φ Real.goldenRatio
  -- (7 - 3√5)/2 ≤ (7 + √5)/2 iff -3√5 ≤ √5 iff -4√5 ≤ 0
  linarith

/-- Auxiliary: ||−3 + 3ζ₅ − 2ζ₅² + ζ₅⁴||² ≤ 3 + φ.
    We compute the normSq and show it's bounded. -/
lemma normSq_A4_at_neg1_le_three_plus_phi :
    Complex.normSq ((-3 : ℂ) + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4) ≤ 3 + φ := by
  rw [normSq_A4_at_neg1]
  -- sin(2π/5) = sin(π/5) * (1+√5)/2
  have h_sin_double : Real.sin (2 * π / 5) = Real.sin (π / 5) * (1 + √5) / 2 := by
    rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring, Real.sin_two_mul]
    rw [Real.cos_pi_div_five]
    ring
  -- 2*sin(2π/5) - 2*sin(π/5) = 2*sin(π/5)*((1+√5)/2 - 1) = sin(π/5)*(√5-1)
  have h_im_simp : 2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5) = Real.sin (π / 5) * (√5 - 1) := by
    rw [h_sin_double]
    ring
  have h_sin_pi5_sq : Real.sin (π / 5)^2 = (5 - √5) / 8 := sin_sq_pi_div_5
  have h_sqrt5_minus_1_sq : (√5 - 1)^2 = 6 - 2*√5 := by nlinarith [sqrt5_sq]
  -- Im² = sin²(π/5) * (√5-1)² = ((5-√5)/8) * (6-2√5) = (5-√5)(6-2√5)/8
  -- = (30 - 10√5 - 6√5 + 2*5)/8 = (40 - 16√5)/8 = 5 - 2√5
  have h_im_sq : (2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5))^2 = 5 - 2*√5 := by
    rw [h_im_simp]
    have h_sq_mul : (Real.sin (π / 5) * (√5 - 1))^2 = Real.sin (π / 5)^2 * (√5 - 1)^2 := by ring
    rw [h_sq_mul, h_sin_pi5_sq, h_sqrt5_minus_1_sq]
    nlinarith [sqrt5_sq]
  -- Re² = ((-7+3√5)/2)² = (49 - 42√5 + 9*5)/4 = (94 - 42√5)/4 = (47 - 21√5)/2
  have h_re_sq : ((-7 + 3*√5) / 2)^2 = (47 - 21*√5) / 2 := by nlinarith [sqrt5_sq]
  -- Total = (47 - 21√5)/2 + 5 - 2√5 = (47 - 21√5)/2 + (10 - 4√5)/2 = (57 - 25√5)/2
  -- 3 + φ = 3 + (1+√5)/2 = (7+√5)/2
  -- Need to show: (47 - 21√5)/2 + 5 - 2√5 ≤ (7+√5)/2
  -- (47 - 21√5 + 10 - 4√5)/2 ≤ (7+√5)/2
  -- 57 - 25√5 ≤ 7 + √5
  -- 50 ≤ 26√5
  -- 25 ≤ 13√5
  -- 25/13 ≤ √5 <=> 625/169 ≤ 5 <=> 625 ≤ 845  TRUE
  calc ((-7 + 3*√5) / 2)^2 + (2*Real.sin (2 * π / 5) - 2*Real.sin (π / 5))^2
      = (47 - 21*√5) / 2 + (5 - 2*√5) := by rw [h_re_sq, h_im_sq]
    _ ≤ (7 + √5) / 2 := by nlinarith [Real.sqrt_nonneg 5]
    _ = 3 + φ := by unfold φ Real.goldenRatio; ring

/-- For c in [-1, (1-sqrt5)/2], the z4 norm is bounded by r_crit.

The quadratic f(c) = ||A4 + cB4||² has vertex at c_v = (5 - 3√5)/4 ≈ -0.43.
Since -1 < (1-√5)/2 ≈ -0.618 < (5-3√5)/4 ≈ -0.43 = vertex,
the interval [-1, (1-√5)/2] is entirely to the LEFT of the vertex.
Since the parabola opens upward, f is DECREASING on [-1, (1-√5)/2].
Therefore the maximum is at c = -1 (left endpoint).
-/
lemma cross_disk_z4_bound_restricted (c : ℝ) (hc_lo : -1 ≤ c) (hc_hi : c ≤ (1 - √5) / 2) :
    ‖(-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 + (c : ℂ) * (1 - ζ₅)‖ ≤ r_crit := by
  set A : ℂ := -2 + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 with hA_def
  set B : ℂ := 1 - ζ₅ with hB_def

  rw [show r_crit = Real.sqrt (3 + φ) by unfold r_crit; rfl]
  have h3φ_pos : 0 < 3 + φ := by unfold φ; linarith [goldenRatio_pos]
  rw [Real.le_sqrt (norm_nonneg _) (le_of_lt h3φ_pos)]

  have h_sqrt5_sq : √5^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

  -- At c = -1: A - B = -3 + 3ζ₅ - 2ζ₅² + ζ₅⁴
  have h_at_neg1 : ‖A + ((-1 : ℝ) : ℂ) * B‖^2 ≤ 3 + φ := by
    have h_neg1 : ((-1 : ℝ) : ℂ) * B = -B := by simp
    rw [h_neg1]
    have h_expr : A + -B = -2 + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 - (1 - ζ₅) := by rw [hA_def, hB_def]; ring
    have h_expr' : A + -B = -3 + 3*ζ₅ - 2*ζ₅^2 + ζ₅^4 := by rw [h_expr]; ring
    rw [← Complex.normSq_eq_norm_sq, h_expr']
    exact normSq_A4_at_neg1_le_three_plus_phi

  -- f(c) ≤ f(-1) since f is decreasing on [-1, c_upper] and c ≥ -1
  have h_mono : ‖A + (c : ℂ) * B‖^2 ≤ ‖A + ((-1 : ℝ) : ℂ) * B‖^2 := by
    rw [hA_def, hB_def]
    simp only [← Complex.normSq_eq_norm_sq]

    -- Expand f(t) = ||A + tB||² = ||A||² + 2t*Re(A*conj(B)) + t²*||B||²
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

    -- Since c ∈ [-1, (1-√5)/2], we have 1+c ≥ 0 and 1-c ≥ (1+√5)/2 > 0.
    have h_c_plus_1_nonneg : 0 ≤ c + 1 := by linarith
    have h_one_minus_c : (1 + √5) / 2 ≤ 1 - c := by linarith

    -- (1-c)*(5-√5)/2 ≥ ((1+√5)/2)*((5-√5)/2) = √5
    have h_prod_lower : √5 ≤ (1 - c) * ((5 - √5) / 2) := by
      have h_5_minus_sqrt5_pos : 0 < (5 - √5) / 2 := by nlinarith [Real.sqrt_nonneg 5]
      have h_prod : ((1 + √5) / 2) * ((5 - √5) / 2) = √5 := by nlinarith [h_sqrt5_sq]
      calc √5 = ((1 + √5) / 2) * ((5 - √5) / 2) := h_prod.symm
        _ ≤ (1 - c) * ((5 - √5) / 2) := by
          apply mul_le_mul_of_nonneg_right h_one_minus_c (le_of_lt h_5_minus_sqrt5_pos)

    -- The second factor is POSITIVE, so f(-1) - f(c) ≥ 0, i.e., f(c) ≤ f(-1)
    have h_second_factor_pos : 0 ≤ -(5*√5 - 10) + (1 - c) * ((5 - √5) / 2) := by
      have h_lower : 10 - 4*√5 ≤ -(5*√5 - 10) + (1 - c) * ((5 - √5) / 2) := by
        calc -(5*√5 - 10) + (1 - c) * ((5 - √5) / 2)
            = (10 - 5*√5) + (1 - c) * ((5 - √5) / 2) := by ring
          _ ≥ (10 - 5*√5) + √5 := by linarith [h_prod_lower]
          _ = 10 - 4*√5 := by ring
      have h_pos : 0 < 10 - 4*√5 := by nlinarith [h_sqrt5_sq]
      linarith

    -- f(-1) - f(c) = (1+c) * second_factor ≥ 0, which implies f(c) ≤ f(-1)
    have h_diff_nonneg : 0 ≤ (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*(-1)*((5*√5 - 10) / 2) + (-1)^2*((5 - √5) / 2)) -
         (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*c*((5*√5 - 10) / 2) + c^2*((5 - √5) / 2)) := by
      calc (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*(-1)*((5*√5 - 10) / 2) + (-1)^2*((5 - √5) / 2)) -
           (Complex.normSq ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4) + 2*c*((5*√5 - 10) / 2) + c^2*((5 - √5) / 2))
          = (c + 1) * (-(5*√5 - 10) + (1 - c) * ((5 - √5) / 2)) := by ring
        _ ≥ 0 := mul_nonneg h_c_plus_1_nonneg h_second_factor_pos
    linarith

  calc ‖A + (c : ℂ) * B‖^2 ≤ ‖A + ((-1 : ℝ) : ℂ) * B‖^2 := h_mono
    _ ≤ 3 + φ := h_at_neg1

end TDCSG.CompoundSymmetry.GG5
