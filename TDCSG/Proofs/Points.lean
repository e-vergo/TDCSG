/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Cyclotomic
import TDCSG.Definitions.Points
import TDCSG.Proofs.Zeta5

/-!
# Fundamental Points for GG(5,5) - Proofs

This file contains the proofs about the points E, E', F, G.
The definitions themselves are in TDCSG.Definitions.Points.

Contains proofs about:
- Point membership in disks
- Segment parameterization
- Ordering properties
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-! ### E Real and Imaginary Parts -/

/-- E.re = √5/2 -/
lemma E_re : E.re = Real.sqrt 5 / 2 := by
  unfold E
  simp only [Complex.sub_re]
  rw [zeta5_re, zeta5_sq_re]
  ring

/-- E.im = sin(2π/5) - sin(4π/5) -/
lemma E_im : E.im = Real.sin (2 * π / 5) - Real.sin (4 * π / 5) := by
  unfold E
  simp only [Complex.sub_im]
  rw [zeta5_im_eq_sin]
  have h2 := zeta5_sq_eq
  rw [h2]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ### Point Properties -/

/-- Compute real part of E + 1 -/
private lemma E_plus_one_re : (E + 1).re = 1 + Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
  unfold E
  have h1 := zeta5_eq
  have h2 := zeta5_sq_eq
  calc (ζ₅ - ζ₅ ^ 2 + 1).re
      = (1 + ζ₅ - ζ₅^2).re := by ring_nf
    _ = (1 + (↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5))) -
        (↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5)))).re := by rw [← h1, ← h2]
    _ = 1 + Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
                 Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero]
      ring

/-- Compute imaginary part of E + 1 -/
private lemma E_plus_one_im : (E + 1).im = Real.sin (2 * π / 5) - Real.sin (4 * π / 5) := by
  unfold E
  have h1 := zeta5_eq
  have h2 := zeta5_sq_eq
  calc (ζ₅ - ζ₅ ^ 2 + 1).im
      = (1 + ζ₅ - ζ₅^2).im := by ring_nf
    _ = (1 + (↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5))) -
        (↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5)))).im := by rw [← h1, ← h2]
    _ = Real.sin (2 * π / 5) - Real.sin (4 * π / 5) := by
      simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
                 Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_add, mul_zero]

/-- Trigonometric identity: sin(4*pi/5) = sin(pi/5) -/
private lemma sin_four_pi_fifth : Real.sin (4 * π / 5) = Real.sin (π / 5) := by
  rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.sin_pi_sub]

/-- sin(2*pi/5) in terms of sin(pi/5) and cos(pi/5) -/
private lemma sin_two_pi_fifth : Real.sin (2 * π / 5) = 2 * Real.sin (π / 5) * Real.cos (π / 5) := by
  rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring]
  exact Real.sin_two_mul (π / 5)

/-- E lies on the LEFT disk boundary (per paper: |E + 1| = r). -/
lemma E_on_left_disk_boundary : ‖E + 1‖ = r_crit := by
  have h_sq : ‖E + 1‖ ^ 2 = 3 + Real.goldenRatio := by
    unfold E
    rw [Complex.sq_norm, Complex.normSq_apply, show (ζ₅ - ζ₅ ^ 2 + 1 : ℂ) = E + 1 by unfold E; ring]
    rw [E_plus_one_re, E_plus_one_im, cos_four_pi_fifth, sin_four_pi_fifth]
    rw [cos_two_pi_fifth, Real.cos_pi_div_five, sin_two_pi_fifth]
    unfold Real.goldenRatio
    have h_re : (1 + ((1 + Real.sqrt 5) / 2 - 1) / 2 - -((1 + Real.sqrt 5) / 4)) =
                (2 + Real.sqrt 5) / 2 := by field_simp; ring
    rw [h_re]
    have h_im_factor : (2 * Real.cos (π / 5) - 1) = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.cos_pi_div_five]; field_simp; ring
    have h_im : (2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5)) =
                Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2 := by
      rw [show 2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5) =
              Real.sin (π / 5) * (2 * Real.cos (π / 5) - 1) by ring, h_im_factor]
      ring
    rw [h_im]
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
    have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    calc (2 + Real.sqrt 5) ^ 2 * 4 ^ 2 + (4 ^ 2 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2
        = (2 + Real.sqrt 5) ^ 2 * 16 + (16 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2 := by norm_num
      _ = (4 + 4 * Real.sqrt 5 + Real.sqrt 5 ^ 2) * 16 +
          (16 - 1 - 2 * Real.sqrt 5 - Real.sqrt 5 ^ 2) * (Real.sqrt 5 ^ 2 - 2 * Real.sqrt 5 + 1) := by ring
      _ = (4 + 4 * Real.sqrt 5 + 5) * 16 +
          (16 - 1 - 2 * Real.sqrt 5 - 5) * (5 - 2 * Real.sqrt 5 + 1) := by rw [h_sqrt5_sq]
      _ = (9 + 4 * Real.sqrt 5) * 16 + (10 - 2 * Real.sqrt 5) * (6 - 2 * Real.sqrt 5) := by ring
      _ = 144 + 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * Real.sqrt 5 ^ 2 := by ring
      _ = 144 + 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * 5 := by rw [h_sqrt5_sq]
      _ = 144 + 60 + 20 + 64 * Real.sqrt 5 - 32 * Real.sqrt 5 := by ring
      _ = 224 + 32 * Real.sqrt 5 := by ring
      _ = 2 * 16 * (6 + (1 + Real.sqrt 5)) := by ring
      _ = 2 * 4 ^ 2 * (2 * 3 + (1 + Real.sqrt 5)) := by norm_num
  rw [← Real.sqrt_sq (norm_nonneg (E + 1)), h_sq]
  rfl

/-- Compute real part of E - 1 -/
private lemma E_minus_one_re : (E - 1).re = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) - 1 := by
  unfold E
  have h1 := zeta5_eq
  have h2 := zeta5_sq_eq
  calc (ζ₅ - ζ₅ ^ 2 - 1).re
      = ((↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5))) -
        (↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5))) - 1).re := by
        rw [← h1, ← h2]
    _ = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) - 1 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring

/-- Compute imaginary part of E - 1 -/
private lemma E_minus_one_im : (E - 1).im = Real.sin (2 * π / 5) - Real.sin (4 * π / 5) := by
  unfold E
  have h1 := zeta5_eq
  have h2 := zeta5_sq_eq
  calc (ζ₅ - ζ₅ ^ 2 - 1).im
      = ((↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5))) -
        (↑(Real.cos (4 * π / 5)) + I * ↑(Real.sin (4 * π / 5))) - 1).im := by
        rw [← h1, ← h2]
    _ = Real.sin (2 * π / 5) - Real.sin (4 * π / 5) := by
      simp only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring

/-- E also lies in the right disk. -/
lemma E_in_right_disk : ‖E - 1‖ ≤ r_crit := by
  -- We compute |E - 1|^2 explicitly and show it's less than r_crit^2
  have h_sq : ‖E - 1‖ ^ 2 < 3 + Real.goldenRatio := by
    unfold E
    rw [Complex.sq_norm, Complex.normSq_apply, show (ζ₅ - ζ₅ ^ 2 - 1 : ℂ) = E - 1 by unfold E; ring]
    rw [E_minus_one_re, E_minus_one_im, cos_four_pi_fifth, sin_four_pi_fifth]
    rw [cos_two_pi_fifth, Real.cos_pi_div_five, sin_two_pi_fifth]
    unfold Real.goldenRatio
    -- Real part: cos(2*pi/5) - (-cos(pi/5)) - 1 = (phi-1)/2 + (1+sqrt5)/4 - 1
    have h_re : (((1 + Real.sqrt 5) / 2 - 1) / 2 - -((1 + Real.sqrt 5) / 4) - 1) =
                (Real.sqrt 5 - 2) / 2 := by field_simp; ring
    rw [h_re]
    -- Imaginary part: sin(2*pi/5) - sin(pi/5) = 2*sin(pi/5)*cos(pi/5) - sin(pi/5)
    have h_im_factor : (2 * Real.cos (π / 5) - 1) = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.cos_pi_div_five]; field_simp; ring
    have h_im : (2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5)) =
                Real.sin (π / 5) * (Real.sqrt 5 - 1) / 2 := by
      rw [show 2 * Real.sin (π / 5) * Real.cos (π / 5) - Real.sin (π / 5) =
              Real.sin (π / 5) * (2 * Real.cos (π / 5) - 1) by ring, h_im_factor]
      ring
    rw [h_im]
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
    have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have h_calc : (Real.sqrt 5 - 2) ^ 2 * 4 ^ 2 + (4 ^ 2 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2
                  = 224 - 96 * Real.sqrt 5 := by
      calc (Real.sqrt 5 - 2) ^ 2 * 4 ^ 2 + (4 ^ 2 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2
          = (Real.sqrt 5 - 2) ^ 2 * 16 + (16 - (1 + Real.sqrt 5) ^ 2) * (Real.sqrt 5 - 1) ^ 2 := by norm_num
        _ = (Real.sqrt 5 ^ 2 - 4 * Real.sqrt 5 + 4) * 16 +
            (16 - 1 - 2 * Real.sqrt 5 - Real.sqrt 5 ^ 2) * (Real.sqrt 5 ^ 2 - 2 * Real.sqrt 5 + 1) := by ring
        _ = (5 - 4 * Real.sqrt 5 + 4) * 16 +
            (16 - 1 - 2 * Real.sqrt 5 - 5) * (5 - 2 * Real.sqrt 5 + 1) := by rw [h_sqrt5_sq]
        _ = (9 - 4 * Real.sqrt 5) * 16 + (10 - 2 * Real.sqrt 5) * (6 - 2 * Real.sqrt 5) := by ring
        _ = 144 - 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * Real.sqrt 5 ^ 2 := by ring
        _ = 144 - 64 * Real.sqrt 5 + 60 - 20 * Real.sqrt 5 - 12 * Real.sqrt 5 + 4 * 5 := by rw [h_sqrt5_sq]
        _ = 144 + 60 + 20 - 96 * Real.sqrt 5 := by ring
        _ = 224 - 96 * Real.sqrt 5 := by ring
    rw [h_calc]
    -- Now show 224 - 96*sqrt5 < 2*16*(3 + (1+sqrt5)/2) = 224 + 32*sqrt5
    have h_target : 2 * 4 ^ 2 * (2 * 3 + (1 + Real.sqrt 5)) = 224 + 32 * Real.sqrt 5 := by norm_num; ring
    rw [h_target]
    -- 224 - 96*sqrt5 < 224 + 32*sqrt5 iff -96*sqrt5 < 32*sqrt5 iff 0 < 128*sqrt5
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

/-! ### Segment Parameter Values -/

/-- Helper: 1 < sqrt5 -/
lemma sqrt5_gt_one : 1 < Real.sqrt 5 := by
  have : (1 : ℝ) ^ 2 < 5 := by norm_num
  calc 1 = Real.sqrt (1 ^ 2) := by simp
       _ < Real.sqrt 5 := by
           apply Real.sqrt_lt_sqrt
           · norm_num
           · exact this

/-- Helper: sqrt5 < 3 -/
lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have : (5 : ℝ) < 3 ^ 2 := by norm_num
  calc Real.sqrt 5 < Real.sqrt (3 ^ 2) := by
           apply Real.sqrt_lt_sqrt
           · norm_num
           · exact this
       _ = 3 := by simp

/-- psi equals the explicit form (√5 - 1) / 2.
    This follows from psi = -goldenConj and goldenConj = (1 - √5) / 2. -/
lemma psi_eq : psi = (Real.sqrt 5 - 1) / 2 := by
  unfold psi Real.goldenConj
  ring

/-- psi is positive. -/
lemma psi_pos : 0 < psi := neg_pos.mpr Real.goldenConj_neg

/-- psi is nonzero. -/
lemma psi_ne_zero : psi ≠ 0 := ne_of_gt psi_pos

/-- psi < 1. -/
lemma psi_lt_one : psi < 1 := by
  rw [psi_eq]
  have h : Real.sqrt 5 < 3 := sqrt5_lt_three
  linarith

/-- psi ≤ 1. -/
lemma psi_le_one : psi ≤ 1 := le_of_lt psi_lt_one

/-- psi is positive (renamed for backward compatibility). -/
lemma t_G_pos : 0 < psi := psi_pos

/-- psi < t_F (since (√5-1)/2 ≈ 0.618 < 0.809 ≈ (1+√5)/4) -/
lemma psi_lt_t_F : psi < t_F := by
  rw [psi_eq]
  unfold t_F
  have sqrt5_bound : Real.sqrt 5 < 3 := sqrt5_lt_three
  rw [show (Real.sqrt 5 - 1) / 2 < (1 + Real.sqrt 5) / 4 ↔
           4 * ((Real.sqrt 5 - 1) / 2) < 4 * ((1 + Real.sqrt 5) / 4) by
      constructor <;> intro h <;> nlinarith [h]]
  field_simp
  linarith

/-- Backward compatibility alias. -/
lemma t_G_lt_t_F : psi < t_F := psi_lt_t_F

/-- t_F < 1 -/
lemma t_F_lt_one : t_F < 1 := by
  unfold t_F
  rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
  calc 1 + Real.sqrt 5
      < 1 + 3 := by linarith [sqrt5_lt_three]
    _ = 4 := by norm_num

/-- ζ₅ + ζ₅⁴ = ψ = (√5-1)/2 (sum of primitive 5th roots of unity). -/
lemma zeta5_plus_zeta5_fourth : ζ₅ + ζ₅^4 = psi := by
  -- zeta5 + zeta5^4 = e^(2*pi*i/5) + e^(-2*pi*i/5) = 2*cos(2*pi/5)
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

/-- Helper: zeta5^2 + zeta5^3 equals negative golden ratio -phi. -/
private lemma zeta5_sq_plus_zeta5_cube : ζ₅^2 + ζ₅^3 = -Real.goldenRatio := by
  -- zeta5^3 = conj(zeta5^2) since zeta5^3 * zeta5^2 = zeta5^5 = 1
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

/-- Helper: phi = 1 + psi -/
private lemma goldenRatio_eq_one_add_psi : Real.goldenRatio = 1 + psi := by
  unfold Real.goldenRatio psi
  field_simp
  ring

/-- Key algebraic identity: 1 = phi*(zeta5 - zeta5^2) + zeta5^3 where phi = goldenRatio. -/
private lemma one_eq_phi_times_E_plus_zeta5_cube :
    (1 : ℂ) = Real.goldenRatio • E + ζ₅^3 := by
  unfold E
  -- Strategy: Use phi = 1 + psi and the factorization psi * (zeta5 - zeta5^2) = 1 - zeta5 + zeta5^2 - zeta5^3
  -- Then phi * (zeta5 - zeta5^2) = (1 + psi) * (zeta5 - zeta5^2) = (zeta5 - zeta5^2) + psi * (zeta5 - zeta5^2)
  --                      = (zeta5 - zeta5^2) + (1 - zeta5 + zeta5^2 - zeta5^3) = 1 - zeta5^3
  -- So: 1 = phi * (zeta5 - zeta5^2) + zeta5^3

  -- From the factorization (zeta5 + zeta5^4)(zeta5 - zeta5^2) = 1 - zeta5 + zeta5^2 - zeta5^3
  -- and zeta5 + zeta5^4 = psi, we have: psi * (zeta5 - zeta5^2) = 1 - zeta5 + zeta5^2 - zeta5^3
  have factorization : (psi : ℂ) • (ζ₅ - ζ₅^2) = 1 - ζ₅ + ζ₅^2 - ζ₅^3 := by
    have h1 := zeta5_plus_zeta5_fourth
    -- Compute: (zeta5 + zeta5^4)(zeta5 - zeta5^2) = zeta5^2 - zeta5^3 + zeta5^5 - zeta5^6
    have h_mult : (ζ₅ + ζ₅^4) * (ζ₅ - ζ₅^2) = ζ₅^2 - ζ₅^3 + ζ₅^5 - ζ₅^6 := by ring
    rw [zeta5_pow_five] at h_mult
    have h6 : ζ₅^6 = ζ₅ := by
      calc ζ₅^6 = ζ₅^5 * ζ₅ := by ring
        _ = 1 * ζ₅ := by rw [zeta5_pow_five]
        _ = ζ₅ := by ring
    rw [h6] at h_mult
    rw [h1] at h_mult
    rw [show ζ₅^2 - ζ₅^3 + (1 : ℂ) - ζ₅ = 1 - ζ₅ + ζ₅^2 - ζ₅^3 by ring] at h_mult
    -- Now convert from multiplication to scalar multiplication
    rw [← smul_eq_mul] at h_mult
    exact h_mult

  -- Now use phi = 1 + psi
  calc (1 : ℂ)
      = (ζ₅ - ζ₅^2) + (1 - ζ₅ + ζ₅^2 - ζ₅^3) + ζ₅^3 := by ring
    _ = (ζ₅ - ζ₅^2) + (psi : ℂ) • (ζ₅ - ζ₅^2) + ζ₅^3 := by
        rw [← factorization]
    _ = (1 : ℂ) • (ζ₅ - ζ₅^2) + (psi : ℂ) • (ζ₅ - ζ₅^2) + ζ₅^3 := by
        simp only [one_smul]
    _ = ((1 : ℂ) + (psi : ℂ)) • (ζ₅ - ζ₅^2) + ζ₅^3 := by
        rw [← add_smul]
    _ = (((1 : ℝ) + psi) : ℂ) • (ζ₅ - ζ₅^2) + ζ₅^3 := by
        congr 1
    _ = (Real.goldenRatio : ℂ) • (ζ₅ - ζ₅^2) + ζ₅^3 := by
        simp only [goldenRatio_eq_one_add_psi]
        norm_cast

/-- F = ψ • E where ψ = (√5-1)/2 (scalar relationship between F and E). -/
lemma F_eq_psi_times_E : F = psi • E := by
  unfold F E
  -- Strategy: Use the factorization (zeta5 + zeta5^4)(zeta5 - zeta5^2) = 1 - zeta5 + zeta5^2 - zeta5^3
  have h1 := zeta5_plus_zeta5_fourth
  -- Compute: (zeta5 + zeta5^4)(zeta5 - zeta5^2) = zeta5^2 - zeta5^3 + zeta5^5 - zeta5^6
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

/-- F lies on the segment E'E. -/
lemma F_on_segment_E'E :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ F = E' + t • (E - E') := by
  use t_F
  constructor
  · -- Show 0 <= t_F
    unfold t_F
    apply div_nonneg
    · linarith [sqrt5_gt_one]
    · norm_num
  constructor
  · -- Show t_F <= 1 (already proven as t_F_lt_one)
    exact t_F_lt_one.le
  · -- Show F = E' + t_F * (E - E')
    unfold E'
    rw [show E - (-E) = 2 • E by simp [two_smul]]
    -- Goal: F = -E + t_F * (2 * E)
    have step1 : t_F • ((2 : ℕ) • E) = (t_F * (2 : ℝ)) • E := by
      rw [show (2 : ℕ) • E = ((2 : ℝ) • E) by norm_cast]
      rw [mul_smul]
    rw [step1]
    -- Goal: F = -E + (2 * t_F) * E = (2 * t_F - 1) * E
    rw [show -E + (t_F * (2 : ℝ)) • E = ((2 * t_F - 1) • E) by
      rw [← neg_one_smul ℝ E, ← add_smul, mul_comm t_F 2, show (-1 : ℝ) + 2 * t_F = 2 * t_F - 1 by ring]]
    -- Show: 2 * t_F - 1 = psi
    have h_param : 2 * t_F - 1 = psi := by
      unfold t_F psi
      field_simp
      ring
    rw [h_param]
    exact F_eq_psi_times_E

/-- G = (√5 - 2) • E (scalar relationship between G and E). -/
lemma G_eq_coeff_times_E : G = ((Real.sqrt 5 - 2) : ℝ) • E := by
  -- Use G = 2F - E and F = psi * E
  unfold G
  rw [F_eq_psi_times_E]
  -- Goal: 2 * psi * E - E = (sqrt5 - 2) * E
  -- First prove the key coefficient identity
  have h_coeff : 2 * psi - 1 = Real.sqrt 5 - 2 := by
    rw [psi_eq]
    field_simp
    ring
  -- Now prove the main goal
  -- Convert 2 * psi * E to (2 * psi) * E first
  have h_smul : (2 : ℂ) * psi • E = ((2 : ℝ) * psi) • E := by
    rw [mul_smul]
    simp [ofReal_ofNat]
  rw [h_smul]
  -- Convert to smul form
  rw [show E = (1 : ℝ) • E by simp]
  simp only [smul_smul, mul_one]
  rw [← sub_smul]
  rw [h_coeff]

/-- G lies on the segment E'E. -/
lemma G_on_segment_E'E :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ G = E' + t • (E - E') := by
  use psi
  constructor
  · exact psi_pos.le
  constructor
  · exact psi_le_one
  · -- Show G = E' + psi * (E - E')
    unfold E'
    rw [show E - (-E) = 2 • E by simp [two_smul]]
    have step1 : psi • ((2 : ℕ) • E) = (psi * (2 : ℝ)) • E := by
      rw [show (2 : ℕ) • E = ((2 : ℝ) • E) by norm_cast]
      rw [mul_smul]
    rw [step1]
    rw [show -E + (psi * (2 : ℝ)) • E = (((-1 : ℝ) + 2 * psi) • E) by
      rw [← neg_one_smul ℝ E, ← add_smul, mul_comm psi 2]]
    have h1 : ((-1 : ℝ) + 2 * psi) = Real.sqrt 5 - 2 := by
      rw [psi_eq]; field_simp; ring
    rw [h1]
    exact G_eq_coeff_times_E

/-- The ordering along the segment: E' < G < F < E.
    Note: G is closer to E' with parameter psi ≈ 0.618,
    while F is closer to E with parameter t_F ≈ 0.809. -/
lemma segment_ordering :
    ∃ (t_F' t_G' : ℝ), 0 < t_G' ∧ t_G' < t_F' ∧ t_F' < 1 ∧
      F = E' + t_F' • (E - E') ∧
      G = E' + t_G' • (E - E') := by
  use t_F, psi
  constructor
  · exact psi_pos
  constructor
  · exact psi_lt_t_F
  constructor
  · exact t_F_lt_one
  constructor
  · -- F = E' + t_F * (E - E')
    unfold E'
    rw [show E - (-E) = 2 • E by simp [two_smul]]
    have step1 : t_F • ((2 : ℕ) • E) = (t_F * (2 : ℝ)) • E := by
      rw [show (2 : ℕ) • E = ((2 : ℝ) • E) by norm_cast]
      rw [mul_smul]
    rw [step1]
    rw [show -E + (t_F * (2 : ℝ)) • E = ((2 * t_F - 1) • E) by
      rw [← neg_one_smul ℝ E, ← add_smul, mul_comm t_F 2, show (-1 : ℝ) + 2 * t_F = 2 * t_F - 1 by ring]]
    have h_param : 2 * t_F - 1 = psi := by
      unfold t_F; rw [psi_eq]; field_simp; ring
    rw [h_param]
    exact F_eq_psi_times_E
  · -- G = E' + psi * (E - E')
    unfold E'
    rw [show E - (-E) = 2 • E by simp [two_smul]]
    have step1 : psi • ((2 : ℕ) • E) = (psi * (2 : ℝ)) • E := by
      rw [show (2 : ℕ) • E = ((2 : ℝ) • E) by norm_cast]
      rw [mul_smul]
    rw [step1]
    rw [show -E + (psi * (2 : ℝ)) • E = (((-1 : ℝ) + 2 * psi) • E) by
      rw [← neg_one_smul ℝ E, ← add_smul, mul_comm psi 2]]
    have h1 : ((-1 : ℝ) + 2 * psi) = Real.sqrt 5 - 2 := by
      rw [psi_eq]; field_simp; ring
    rw [h1]
    exact G_eq_coeff_times_E

end TDCSG.CompoundSymmetry.GG5
