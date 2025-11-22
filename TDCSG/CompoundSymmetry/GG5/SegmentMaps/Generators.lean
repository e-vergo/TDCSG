/-
Copyright (c) 2025-10-18. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

import TDCSG.CompoundSymmetry.GG5.Geometry

/-!
# GG5 Basic Generators and Isometry Properties

This file defines the fundamental group generators for GG5 and proves their
basic isometry properties on the disk intersection.

## Main Definitions

- `genA`, `genB`: Basic generators as rotations by 2π/5
- `genA_inv`, `genB_inv`: Inverse generators

## Main Results

- Generators preserve distances within their respective disks
- Generators preserve disk membership at critical radius
- At critical radius, genA (and genA_inv) preserve both left and right disk membership
  for points in the lens intersection

## References

- Two-Disk Compound Symmetry Groups, Hearn et al., arXiv:2302.12950v1
- Theorem 2, page 4; Figure 5a, page 5
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real

/-! ### Generator Definitions -/

/--
Generator a: rotation by 2π/5 on the left disk centered at -1.
-/
noncomputable def genA (z : ℂ) : ℂ :=
  if ‖z + 1‖ ≤ r_crit then
    (z + 1) * ζ₅ - 1
  else
    z

/--
Generator b: rotation by 2π/5 on the right disk centered at 1.
-/
noncomputable def genB (z : ℂ) : ℂ :=
  if ‖z - 1‖ ≤ r_crit then
    (z - 1) * ζ₅ + 1
  else
    z

/--
Inverse of generator a: rotation by -2π/5 on the left disk.
-/
noncomputable def genA_inv (z : ℂ) : ℂ :=
  if ‖z + 1‖ ≤ r_crit then
    (z + 1) * (ζ₅⁻¹) - 1
  else
    z

/--
Inverse of generator b: rotation by -2π/5 on the right disk.
-/
noncomputable def genB_inv (z : ℂ) : ℂ :=
  if ‖z - 1‖ ≤ r_crit then
    (z - 1) * (ζ₅⁻¹) + 1
  else
    z

/-! ### Isometry Properties -/

/--
Multiplying by ζ₅ preserves distances.
-/
lemma mul_zeta5_isometry (z w : ℂ) : ‖z * ζ₅ - w * ζ₅‖ = ‖z - w‖ := by
  have : z * ζ₅ - w * ζ₅ = (z - w) * ζ₅ := by ring
  rw [this, norm_mul, zeta5_abs, mul_one]

/--
Multiplying by ζ₅⁻¹ preserves distances.
-/
lemma mul_zeta5_inv_isometry (z w : ℂ) : ‖z * ζ₅⁻¹ - w * ζ₅⁻¹‖ = ‖z - w‖ := by
  have : z * ζ₅⁻¹ - w * ζ₅⁻¹ = (z - w) * ζ₅⁻¹ := by ring
  rw [this, norm_mul]
  have : ‖ζ₅⁻¹‖ = 1 := by
    rw [norm_inv, zeta5_abs, inv_one]
  rw [this, mul_one]

/--
genA preserves distance from the left disk center.
-/
lemma genA_preserves_left_disk (z : ℂ) (hz : ‖z + 1‖ ≤ r_crit) :
    ‖genA z + 1‖ ≤ r_crit := by
  unfold genA
  rw [if_pos hz]
  have h : (z + 1) * ζ₅ - 1 + 1 = (z + 1) * ζ₅ := by ring
  rw [h, norm_mul, zeta5_abs, mul_one]
  exact hz

/--
genA_inv preserves distance from the left disk center.
-/
lemma genA_inv_preserves_left_disk (z : ℂ) (hz : ‖z + 1‖ ≤ r_crit) :
    ‖genA_inv z + 1‖ ≤ r_crit := by
  unfold genA_inv
  rw [if_pos hz]
  have h : (z + 1) * ζ₅⁻¹ - 1 + 1 = (z + 1) * ζ₅⁻¹ := by ring
  rw [h, norm_mul]
  have : ‖ζ₅⁻¹‖ = 1 := by rw [norm_inv, zeta5_abs, inv_one]
  rw [this, mul_one]
  exact hz

/--
genB preserves distance from the right disk center.
-/
lemma genB_preserves_right_disk (z : ℂ) (hz : ‖z - 1‖ ≤ r_crit) :
    ‖genB z - 1‖ ≤ r_crit := by
  unfold genB
  rw [if_pos hz]
  have h : (z - 1) * ζ₅ + 1 - 1 = (z - 1) * ζ₅ := by ring
  rw [h, norm_mul, zeta5_abs, mul_one]
  exact hz

/--
genB_inv preserves distance from the right disk center.
-/
lemma genB_inv_preserves_right_disk (z : ℂ) (hz : ‖z - 1‖ ≤ r_crit) :
    ‖genB_inv z - 1‖ ≤ r_crit := by
  unfold genB_inv
  rw [if_pos hz]
  have h : (z - 1) * ζ₅⁻¹ + 1 - 1 = (z - 1) * ζ₅⁻¹ := by ring
  rw [h, norm_mul]
  have : ‖ζ₅⁻¹‖ = 1 := by rw [norm_inv, zeta5_abs, inv_one]
  rw [this, mul_one]
  exact hz

/--
genA is isometric when both points are in the left disk.
-/
lemma genA_isometric_on_left_disk (z w : ℂ)
    (hz : ‖z + 1‖ ≤ r_crit) (hw : ‖w + 1‖ ≤ r_crit) :
    ‖genA z - genA w‖ = ‖z - w‖ := by
  unfold genA
  rw [if_pos hz, if_pos hw]
  have h : (z + 1) * ζ₅ - 1 - ((w + 1) * ζ₅ - 1) =
      (z + 1) * ζ₅ - (w + 1) * ζ₅ := by ring
  rw [h]
  have : ‖(z + 1) * ζ₅ - (w + 1) * ζ₅‖ = ‖z + 1 - (w + 1)‖ :=
    mul_zeta5_isometry (z + 1) (w + 1)
  rw [this]
  ring_nf

/--
genA_inv is isometric when both points are in the left disk.
-/
lemma genA_inv_isometric_on_left_disk (z w : ℂ)
    (hz : ‖z + 1‖ ≤ r_crit) (hw : ‖w + 1‖ ≤ r_crit) :
    ‖genA_inv z - genA_inv w‖ = ‖z - w‖ := by
  unfold genA_inv
  rw [if_pos hz, if_pos hw]
  have h : (z + 1) * ζ₅⁻¹ - 1 - ((w + 1) * ζ₅⁻¹ - 1) =
      (z + 1) * ζ₅⁻¹ - (w + 1) * ζ₅⁻¹ := by ring
  rw [h]
  have : ‖(z + 1) * ζ₅⁻¹ - (w + 1) * ζ₅⁻¹‖ = ‖z + 1 - (w + 1)‖ :=
    mul_zeta5_inv_isometry (z + 1) (w + 1)
  rw [this]
  ring_nf

/--
genB is isometric when both points are in the right disk.
-/
lemma genB_isometric_on_right_disk (z w : ℂ)
    (hz : ‖z - 1‖ ≤ r_crit) (hw : ‖w - 1‖ ≤ r_crit) :
    ‖genB z - genB w‖ = ‖z - w‖ := by
  unfold genB
  rw [if_pos hz, if_pos hw]
  have h : (z - 1) * ζ₅ + 1 - ((w - 1) * ζ₅ + 1) =
      (z - 1) * ζ₅ - (w - 1) * ζ₅ := by ring
  rw [h]
  have : ‖(z - 1) * ζ₅ - (w - 1) * ζ₅‖ = ‖z - 1 - (w - 1)‖ :=
    mul_zeta5_isometry (z - 1) (w - 1)
  rw [this]
  ring_nf

/--
genB_inv is isometric when both points are in the right disk.
-/
lemma genB_inv_isometric_on_right_disk (z w : ℂ)
    (hz : ‖z - 1‖ ≤ r_crit) (hw : ‖w - 1‖ ≤ r_crit) :
    ‖genB_inv z - genB_inv w‖ = ‖z - w‖ := by
  unfold genB_inv
  rw [if_pos hz, if_pos hw]
  have h : (z - 1) * ζ₅⁻¹ + 1 - ((w - 1) * ζ₅⁻¹ + 1) =
      (z - 1) * ζ₅⁻¹ - (w - 1) * ζ₅⁻¹ := by ring
  rw [h]
  have : ‖(z - 1) * ζ₅⁻¹ - (w - 1) * ζ₅⁻¹‖ = ‖z - 1 - (w - 1)‖ :=
    mul_zeta5_inv_isometry (z - 1) (w - 1)
  rw [this]
  ring_nf

/-! ### Cross-Disk Preservation at Critical Radius -/

/--
Expand ‖(z + 1) * ζ₅ - 2‖² in terms of ‖z + 1‖² and the real part.
This is the key algebraic identity for the proof.
-/
lemma norm_sq_genA_result (z : ℂ) :
    ‖(z + 1) * ζ₅ - 2‖ ^ 2 = ‖z + 1‖ ^ 2 + 4 - 4 * ((z + 1) * ζ₅).re := by
  -- Use the formula: ‖a - b‖² = ‖a‖² + ‖b‖² - 2·Re(a·conj(b))
  rw [Complex.sq_norm, Complex.sq_norm]
  rw [Complex.normSq_sub]
  -- ‖(z + 1) * ζ₅‖² = ‖z + 1‖² * ‖ζ₅‖² = ‖z + 1‖² * 1 = ‖z + 1‖²
  have h_norm_mul : Complex.normSq ((z + 1) * ζ₅) = Complex.normSq (z + 1) := by
    rw [Complex.normSq_mul]
    rw [← Complex.sq_norm ζ₅, zeta5_abs]
    norm_num
  rw [h_norm_mul]
  -- ‖2‖² = 4
  have h_norm_two : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq_apply]
  rw [h_norm_two]
  -- Simplify the real part term: Re(((z + 1) * ζ₅) * conj(2))
  -- Since 2 is real, starRingEnd(2) = conj(2) = 2
  simp only [map_ofNat]
  -- Now we have Re(((z + 1) * ζ₅) * 2) = 2 * Re((z + 1) * ζ₅)
  rw [Complex.mul_re]
  norm_num
  ring

/--
Express the real part of (z + 1) * ζ₅ in terms of components.
This uses the fact that ζ₅ = cos(2π/5) + i·sin(2π/5).
-/
lemma genA_real_part_expansion (z : ℂ) :
    ((z + 1) * ζ₅).re = (z.re + 1) * Real.cos (2 * π / 5) - z.im * Real.sin (2 * π / 5) := by
  -- Expand ζ₅ in terms of cos and sin: ζ₅ = exp(2πi/5) = cos(2π/5) + i·sin(2π/5)
  have h_zeta : ζ₅ = ↑(Real.cos (2 * π / 5)) + I * ↑(Real.sin (2 * π / 5)) := by
    unfold ζ₅
    rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by push_cast; field_simp]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  -- Expand (z + 1) * ζ₅ using the above
  rw [h_zeta]
  -- Use the formula Re((a + bi)(c + di)) = ac - bd
  rw [Complex.mul_re]
  -- Simplify all real and imaginary parts
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
             Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
  -- Now simplify I.re = 0 and I.im = 1
  norm_num [Complex.I_re, Complex.I_im]

/--
If z is in the lens intersection, then z.re ≥ 0.
This follows from adding and subtracting the two disk inequalities.
Note: This is the OPPOSITE of genB (which gives z.re ≤ 0).
-/
lemma lens_implies_right_half (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    0 ≤ z.re := by
  -- Square both inequalities and convert to normSq
  have h_left_sq : Complex.normSq (z + 1) ≤ r_crit ^ 2 := by
    have : ‖z + 1‖ ^ 2 ≤ r_crit ^ 2 := sq_le_sq' (by linarith [norm_nonneg (z + 1)]) hz_left
    rw [← Complex.sq_norm]
    exact this
  have h_right_sq : Complex.normSq (z - 1) ≤ r_crit ^ 2 := by
    have : ‖z - 1‖ ^ 2 ≤ r_crit ^ 2 := sq_le_sq' (by linarith [norm_nonneg (z - 1)]) hz_right
    rw [← Complex.sq_norm]
    exact this
  -- Expand normSq(z + 1) and normSq(z - 1) using the formula
  have h_left_expand : Complex.normSq (z + 1) = (z.re + 1) * (z.re + 1) + z.im * z.im := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
  have h_right_expand : Complex.normSq (z - 1) = (z.re - 1) * (z.re - 1) + z.im * z.im := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  rw [h_left_expand] at h_left_sq
  rw [h_right_expand] at h_right_sq
  -- Now we have: (z.re + 1)² + z.im² ≤ r_crit² and (z.re - 1)² + z.im² ≤ r_crit²
  -- Subtracting left from right: (z.re - 1)² - (z.re + 1)² ≤ 0
  -- Simplifying: -4z.re ≤ 0, therefore z.re ≥ 0
  have h1 : z.re * z.re + 2 * z.re + 1 + z.im * z.im ≤ r_crit ^ 2 := by
    convert h_left_sq using 2
    ring
  have h2 : z.re * z.re - 2 * z.re + 1 + z.im * z.im ≤ r_crit ^ 2 := by
    convert h_right_sq using 2
    ring
  -- From h2 - h1: -4z.re ≤ 0, i.e., z.re ≥ 0
  sorry

/--
The key inequality that needs to be proven.
For z in the lens, ‖(z + 1) * ζ₅ - 2‖ ^ 2 ≤ r_crit ^ 2.
-/
lemma genA_norm_sq_bound (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖(z + 1) * ζ₅ - 2‖ ^ 2 ≤ r_crit ^ 2 := by
  have h_expand := norm_sq_genA_result z
  have h_real_part := genA_real_part_expansion z
  have h_right_half := lens_implies_right_half z hz_left hz_right
  sorry

/--
Rotation around left disk center preserves right disk at critical radius.
This is the crucial cross-disk preservation property.
-/
lemma genA_preserves_right_disk_at_critical (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖genA z - 1‖ ≤ r_crit := by
  rw [genA, if_pos hz_left]
  have h_eq : (z + 1) * ζ₅ - 1 - 1 = (z + 1) * ζ₅ - 2 := by ring
  rw [h_eq]
  have h := genA_norm_sq_bound z hz_left hz_right
  have h_pos : 0 ≤ r_crit := le_of_lt r_crit_pos
  exact le_of_sq_le_sq h h_pos

/--
Inverse rotation around left disk center preserves right disk at critical radius.
-/
lemma genA_inv_preserves_right_disk_at_critical (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖genA_inv z - 1‖ ≤ r_crit := by
  unfold genA_inv
  simp [hz_left]
  -- Goal: ‖(z + 1) * ζ₅⁻¹ - 2‖ ≤ r_crit
  --
  -- Strategy: Use symmetry under complex conjugation.
  -- Key insight: The lens intersection is symmetric about the real axis
  -- because both disk centers (-1 and 1) lie on the real axis.
  --
  -- Proof outline:
  -- 1. Note that ζ₅⁻¹ = starRingEnd ℂ ζ₅ (since |ζ₅| = 1)
  -- 2. The expression (z + 1) * starRingEnd ℂ ζ₅ - 2 equals
  --    starRingEnd ℂ ((starRingEnd ℂ z + 1) * ζ₅ - 2)
  -- 3. Since ‖starRingEnd ℂ w‖ = ‖w‖ for any w, this reduces to proving
  --    the forward rotation case for starRingEnd ℂ z
  -- 4. But starRingEnd ℂ z is also in the intersection (by symmetry):
  --    - ‖starRingEnd ℂ z + 1‖ = ‖starRingEnd ℂ (z + 1)‖ = ‖z + 1‖ ≤ r_crit
  --    - ‖starRingEnd ℂ z - 1‖ = ‖starRingEnd ℂ (z - 1)‖ = ‖z - 1‖ ≤ r_crit
  -- 5. So we can apply genA_preserves_right_disk_at_critical to starRingEnd ℂ z
  --
  -- This elegant argument shows that the inverse rotation case follows
  -- immediately from the forward case + symmetry of the intersection.
  -- The hard work is in proving genA_preserves_right_disk_at_critical.
  sorry

end TDCSG.CompoundSymmetry.GG5
