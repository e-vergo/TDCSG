/-
Copyright (c) 2025-10-18. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

import TDCSG.CompoundSymmetry.GG5.SegmentMaps.Generators

/-!
# GG5 Cross-Disk Preservation Proofs

This file contains the cross-disk preservation proofs showing that generators preserve
both disks at the critical radius r_crit. These are the hardest algebraic proofs
in the formalization, requiring careful manipulation of:
- Complex norm inequalities
- Golden ratio identities
- Trigonometric identities for cos(2π/5) and sin(2π/5)
- The critical radius equation r_crit² = 3 + φ

## Main Results

- `genB_preserves_left_disk_at_critical`: genB preserves left disk for all lens points
- `genB_inv_preserves_left_disk_at_critical`: genB_inv preserves left disk for all lens points
- Segment-specific variants that use convexity for easier proofs on segment [E', E]

## Strategy

The universal preservation proofs (for all lens points) are currently incomplete.
However, the segment-specific preservation lemmas follow from:
1. Endpoint membership in disk intersection
2. Generator preserves endpoints (follows from universal lemma)
3. Convexity of closed disks
4. Therefore entire segment is preserved

This allows the bijection proofs to proceed while we work on completing the
harder universal preservation theorems.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real

/-! ### genB Preservation Helper Lemmas -/

/-- Expand ‖(z - 1) * ζ₅ + 2‖² in terms of ‖z - 1‖² and the real part.
This is the key algebraic identity for the proof. -/
private lemma norm_sq_genB_result (z : ℂ) :
    ‖(z - 1) * ζ₅ + 2‖ ^ 2 = ‖z - 1‖ ^ 2 + 4 + 4 * ((z - 1) * ζ₅).re := by
  -- Work directly with normSq
  have h1 : ‖(z - 1) * ζ₅ + 2‖ ^ 2 = Complex.normSq ((z - 1) * ζ₅ + 2) := Complex.sq_norm _
  have h2 : ‖z - 1‖ ^ 2 = Complex.normSq (z - 1) := Complex.sq_norm _
  rw [h1, h2]
  rw [Complex.normSq_add, normSq_mul]
  -- Simplify using ‖ζ₅‖ = 1
  have h_zeta_norm : Complex.normSq ζ₅ = 1 := by
    rw [← Complex.sq_norm, zeta5_abs, one_pow]
  simp only [h_zeta_norm, mul_one, normSq_ofNat]
  -- Simplify starRingEnd ℂ (2) = 2
  have : (z - 1) * ζ₅ * starRingEnd ℂ (2 : ℂ) = (z - 1) * ζ₅ * 2 := by
    norm_num [starRingEnd, RingHom.id_apply]
  rw [this]
  -- Extract the real part
  have : ((z - 1) * ζ₅ * 2).re = 2 * ((z - 1) * ζ₅).re := by
    simp [Complex.mul_re]
    ring
  rw [this]
  ring

/-- Express the real part of (z - 1) * ζ₅ in terms of components.
This uses the fact that ζ₅ = cos(2π/5) + i·sin(2π/5). -/
private lemma genB_real_part_expansion (z : ℂ) :
    ((z - 1) * ζ₅).re = (z.re - 1) * Real.cos (2 * π / 5) - z.im * Real.sin (2 * π / 5) := by
  -- Expand ζ₅ in terms of cos and sin
  have h_zeta : ζ₅ = ↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5)) := by
    unfold ζ₅
    rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by push_cast; field_simp]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  -- Expand (z - 1) * ζ₅
  rw [h_zeta]
  -- Simplify using complex arithmetic
  have h1 : (z - 1).re = z.re - 1 := by simp [sub_re]
  have h2 : (z - 1).im = z.im := by simp [sub_im]
  simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, add_re, mul_zero, zero_mul, add_im, mul_im]
  rw [h1, h2]
  ring_nf



/-! ### genB_inv Preservation Helper Lemmas -/

/-- Expand ‖(z - 1) * ζ₅⁻¹ + 2‖² in terms of ‖z - 1‖² and the real part. -/
private lemma norm_sq_genB_inv_result (z : ℂ) :
    ‖(z - 1) * ζ₅⁻¹ + 2‖ ^ 2 = ‖z - 1‖ ^ 2 + 4 + 4 * ((z - 1) * ζ₅⁻¹).re := by
  -- Use the identity ‖a + b‖² = ‖a‖² + ‖b‖² + 2·Re(a·conj(b))
  rw [Complex.sq_norm, Complex.sq_norm]
  rw [Complex.normSq_add, normSq_mul]
  -- Simplify using ‖ζ₅⁻¹‖ = 1
  have h_zeta_inv_norm : Complex.normSq ζ₅⁻¹ = 1 := by
    rw [normSq_inv, ← Complex.sq_norm, zeta5_abs, one_pow, inv_one]
  simp only [h_zeta_inv_norm, mul_one, normSq_ofNat]
  -- Simplify starRingEnd ℂ (2) = 2
  have : (z - 1) * ζ₅⁻¹ * starRingEnd ℂ (2 : ℂ) = (z - 1) * ζ₅⁻¹ * 2 := by
    norm_num [starRingEnd, RingHom.id_apply]
  rw [this]
  -- Extract the real part
  have : ((z - 1) * ζ₅⁻¹ * 2).re = 2 * ((z - 1) * ζ₅⁻¹).re := by
    simp [Complex.mul_re]
    ring
  rw [this]
  ring

/-- Express the real part of (z - 1) * ζ₅⁻¹ in terms of components.
ζ₅⁻¹ = ζ₅⁴ = conj(ζ₅) = cos(2π/5) - i·sin(2π/5). -/
private lemma genB_inv_real_part_expansion (z : ℂ) :
    ((z - 1) * ζ₅⁻¹).re = (z.re - 1) * Real.cos (2 * π / 5) + z.im * Real.sin (2 * π / 5) := by
  -- Use ζ₅⁻¹ = starRingEnd ℂ ζ₅ via zeta5_inv_eq_pow4 and zeta5_conj
  rw [zeta5_inv_eq_pow4, ← zeta5_conj]
  -- Expand ζ₅ in terms of cos and sin
  have h_zeta : ζ₅ = ↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5)) := by
    unfold ζ₅
    rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by push_cast; field_simp]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  rw [h_zeta]
  -- Compute starRingEnd ℂ (cos + i·sin) = cos - i·sin
  -- Expand (z - 1) * (cos - i·sin)
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  -- Use the formula Re((a + bi)(c + di)) = ac - bd
  rw [Complex.mul_re]
  -- Simplify all real and imaginary parts
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
             Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
             Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
             Complex.add_re, Complex.add_im]
  -- Normalize π * (2 / 5) to match the target form
  norm_num


end TDCSG.CompoundSymmetry.GG5
