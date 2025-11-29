/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Conversions
import TDCSG.Definitions.Geometry
import TDCSG.Definitions.Core
import TDCSG.Proofs.Points
import TDCSG.MainTheorem
import TDCSG.Proofs.SegmentGeometry

/-!
# Complex to Plane Conversion for GG(5,5) - Proofs

Proofs about conversions between complex numbers and Plane (ℝ²), rotation correspondence,
and disk membership lemmas.

The conversion definitions are in TDCSG.Definitions.Conversions.

## Main Definitions

* `toPlane` : Convert a complex number to a Plane (ℝ²) point
* `fromPlane` : Convert a Plane point to a complex number
* `segmentPoint` : Parameterize segment E'E by t ∈ [0,1]
* `segmentPointPlane` : Same parameterization in Plane coordinates

## Main Results

* `E'_on_right_disk_boundary` : E' is on the right disk boundary
* `E'_in_left_disk` : E' is in the left disk
* `segment_in_disk_intersection` : Points on segment E'E lie in both disks
* `toPlane_fromPlane` : toPlane and fromPlane are inverses
* `zeta5_rotation_eq_rotateAroundPoint` : ζ₅ multiplication corresponds to rotation by 2π/5
* `zeta5_pow4_rotation_eq_rotateAroundPoint` : ζ₅⁴ multiplication corresponds to rotation by -2π/5
* `genA_eq_zeta5_pow4_rotation` : genA equals ζ₅⁴ rotation about -1 (clockwise)
* `genB_eq_zeta5_pow4_rotation` : genB equals ζ₅⁴ rotation about 1 (clockwise)

-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real TDCSG.Definitions

/-! ### Basic conversion lemmas -/

/-- Addition in complex numbers corresponds to addition in Plane. -/
lemma toPlane_add (z w : ℂ) : toPlane (z + w) = toPlane z + toPlane w := by
  unfold toPlane
  ext i
  fin_cases i <;> simp [Complex.add_re, Complex.add_im]

/-- Subtraction in complex numbers corresponds to subtraction in Plane. -/
lemma toPlane_sub (z w : ℂ) : toPlane (z - w) = toPlane z - toPlane w := by
  unfold toPlane
  ext i
  fin_cases i <;> simp [Complex.sub_re, Complex.sub_im]

/-- Distance in Plane equals complex norm. -/
lemma toPlane_dist_eq_complex_norm (z w : ℂ) : dist (toPlane z) (toPlane w) = ‖z - w‖ := by
  unfold toPlane
  rw [dist_comm, EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dist_comm (w.re), dist_comm (w.im)]
  simp only [Real.dist_eq]
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.sub_re, Complex.sub_im]
  congr 1
  simp only [sq_abs]

/-! ### Disk Intersection -/

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

/-- Compute real part of E in trigonometric form (E = ζ₅⁴ - ζ₅³)
    Note: ζ₅⁴ and ζ₅³ are conjugates of ζ₅ and ζ₅², so the real part is the same. -/
private lemma E_re_trig : E.re = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
  unfold E
  simp only [Complex.sub_re]
  -- ζ₅⁴.re = ζ₅.re and ζ₅³.re = ζ₅².re (conjugate pairs have same real part)
  have h4 : (ζ₅^4).re = ζ₅.re := by rw [← zeta5_conj]; rfl
  have h3 : (ζ₅^3).re = (ζ₅^2).re := by
    have hconj : ζ₅^3 = starRingEnd ℂ (ζ₅^2) := by
      rw [map_pow, zeta5_conj]
      rw [show (ζ₅^4)^2 = ζ₅^8 by ring, show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta5_pow_five, one_mul]
    rw [hconj]; rfl
  rw [h4, h3, zeta5_re, zeta5_sq_re]
  rw [cos_two_pi_fifth, cos_four_pi_fifth, Real.cos_pi_div_five]
  unfold Real.goldenRatio
  field_simp
  ring

/-- Point E has positive real part.
This is a computationally verifiable fact using E = ζ₅ - ζ₅². -/
lemma E_re_pos : 0 < E.re := by
  rw [E_re_trig, cos_four_pi_fifth, cos_two_pi_fifth, Real.cos_pi_div_five]
  unfold Real.goldenRatio
  -- E.re = (φ - 1)/2 - (-cos(π/5)) = ((1+√5)/2 - 1)/2 + (1+√5)/4
  --      = (√5 - 1)/4 + (1+√5)/4 = √5/2 > 0
  have h : ((1 + Real.sqrt 5) / 2 - 1) / 2 - -((1 + Real.sqrt 5) / 4) = Real.sqrt 5 / 2 := by
    field_simp; ring
  rw [h]
  have sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  linarith

/-- Point E' has negative real part.
This follows immediately from E' = -E and E_re_pos. -/
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

/-! ## Infrastructure for connecting IET orbits to group orbits -/

/-- Complex multiplication as a matrix: multiplying by `a` is the same as
    applying the rotation-scale matrix [[a.re, -a.im], [a.im, a.re]]. -/
lemma complex_mul_as_matrix (a z : ℂ) :
    TDCSG.Definitions.toPlane (a * z) = applyMatrix !![a.re, -a.im; a.im, a.re] (TDCSG.Definitions.toPlane z) := by
  unfold TDCSG.Definitions.toPlane applyMatrix
  ext i
  fin_cases i <;> simp [Complex.mul_re, Complex.mul_im, Fin.sum_univ_two] <;> ring

/-- Rotation in ℂ by ζ₅ corresponds to rotateAroundPoint in Plane.

This is the key lemma connecting complex multiplication to plane rotation:
- In ℂ: rotation around c by 2π/5 maps z to c + ζ₅ * (z - c)
- In Plane: rotateAroundPoint center (2π/5) p uses the rotation matrix
Both are equivalent when we identify ℂ with ℝ² via toPlane/fromPlane.

The proof follows from:
1. ζ₅ = exp(2πi/5) = cos(2π/5) + i·sin(2π/5)
2. Complex multiplication by ζ₅ is rotation in ℝ²
3. The rotation matrix [[cos θ, -sin θ], [sin θ, cos θ]] acts identically -/
theorem zeta5_rotation_eq_rotateAroundPoint (z c : ℂ) :
    TDCSG.Definitions.toPlane (c + ζ₅ * (z - c)) = rotateAroundPoint (TDCSG.Definitions.toPlane c) (2 * π / 5) (TDCSG.Definitions.toPlane z) := by
  -- Unfold rotateAroundPoint definition
  unfold rotateAroundPoint
  -- Use toPlane_add to split the LHS
  rw [toPlane_add]
  -- Now goal: toPlane c + toPlane (ζ₅ * (z - c)) = toPlane c + applyMatrix (rotationMatrix ...) (toPlane z - toPlane c)
  congr 1
  -- Goal: toPlane (ζ₅ * (z - c)) = applyMatrix (rotationMatrix (2*π/5)) (toPlane z - toPlane c)
  -- Use toPlane_sub on the RHS
  rw [← toPlane_sub]
  -- Goal: toPlane (ζ₅ * (z - c)) = applyMatrix (rotationMatrix (2*π/5)) (toPlane (z - c))
  -- Use complex_mul_as_matrix on the LHS
  rw [complex_mul_as_matrix]
  -- Goal: applyMatrix !![ζ₅.re, -ζ₅.im; ζ₅.im, ζ₅.re] (toPlane (z - c)) =
  --       applyMatrix (rotationMatrix (2*π/5)) (toPlane (z - c))
  congr 1
  -- Goal: !![ζ₅.re, -ζ₅.im; ζ₅.im, ζ₅.re] = rotationMatrix (2*π/5)
  unfold rotationMatrix
  -- Goal: !![ζ₅.re, -ζ₅.im; ζ₅.im, ζ₅.re] = !![cos(2*π/5), -sin(2*π/5); sin(2*π/5), cos(2*π/5)]
  rw [zeta5_re_eq_cos, zeta5_im_eq_sin]

/-- (ζ₅⁴).re = cos(2π/5) = cos(-2π/5) -/
private lemma zeta5_pow4_re_eq_cos_neg : (ζ₅^4).re = Real.cos (-2 * π / 5) := by
  have h : -2 * π / 5 = -(2 * π / 5) := by ring
  rw [h, Real.cos_neg, zeta5_pow4_re, cos_two_pi_fifth]
  unfold Real.goldenRatio
  ring

/-- (ζ₅⁴).im = sin(-2π/5) -/
private lemma zeta5_pow4_im_eq_sin_neg : (ζ₅^4).im = Real.sin (-2 * π / 5) := by
  have h : -2 * π / 5 = -(2 * π / 5) := by ring
  rw [h, Real.sin_neg, zeta5_pow4_im_neg, zeta5_im_eq_sin]

/-- Clockwise rotation correspondence: ζ₅⁴ multiplication corresponds to rotation by -2π/5.
Since ζ₅⁴ = ζ₅⁻¹ = exp(-2πi/5), this is the clockwise version of zeta5_rotation_eq_rotateAroundPoint. -/
theorem zeta5_pow4_rotation_eq_rotateAroundPoint (z c : ℂ) :
    TDCSG.Definitions.toPlane (c + ζ₅^4 * (z - c)) = rotateAroundPoint (TDCSG.Definitions.toPlane c) (-2 * π / 5) (TDCSG.Definitions.toPlane z) := by
  unfold rotateAroundPoint
  rw [toPlane_add]
  congr 1
  rw [← toPlane_sub]
  rw [complex_mul_as_matrix]
  congr 1
  unfold rotationMatrix
  rw [zeta5_pow4_re_eq_cos_neg, zeta5_pow4_im_eq_sin_neg]

/-! ### Segment parameterization -/

-- Note: segmentPoint, segmentPointPlane, segmentPoint_eq_scalar_E, segmentPoint_translate
-- are defined in TDCSG.Definitions.Conversions
-- E_ne_zero is imported from TDCSG.SegmentGeometry

/-- The segment parameterization is injective: different parameters give different points. -/
theorem segmentPoint_injective : Function.Injective TDCSG.Definitions.segmentPoint := by
  intro t₁ t₂ h
  unfold TDCSG.Definitions.segmentPoint at h
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
theorem segmentPointPlane_injective : Function.Injective TDCSG.Definitions.segmentPointPlane := by
  intro t₁ t₂ h
  apply segmentPoint_injective
  unfold TDCSG.Definitions.segmentPointPlane TDCSG.Definitions.toPlane at h
  -- If ![z₁.re, z₁.im] = ![z₂.re, z₂.im], then z₁ = z₂
  have hre : (TDCSG.Definitions.segmentPoint t₁).re = (TDCSG.Definitions.segmentPoint t₂).re := by
    have := congrFun h 0
    simp only [Matrix.cons_val_zero] at this
    exact this
  have him : (TDCSG.Definitions.segmentPoint t₁).im = (TDCSG.Definitions.segmentPoint t₂).im := by
    have := congrFun h 1
    simp only [Matrix.cons_val_one] at this
    exact this
  exact Complex.ext hre him

/-! ### Disk membership for segment points -/

-- Note: toPlane_dist_eq_complex_norm is defined in TDCSG.Definitions.Conversions

/-- leftCenterPlane equals toPlane (-1). -/
lemma leftCenterPlane_eq_toPlane : leftCenterPlane = TDCSG.Definitions.toPlane (-1 : ℂ) := by
  unfold leftCenterPlane TDCSG.Definitions.toPlane
  ext i
  fin_cases i <;> simp [Complex.neg_re, Complex.neg_im]

/-- rightCenterPlane equals toPlane (1). -/
lemma rightCenterPlane_eq_toPlane : rightCenterPlane = TDCSG.Definitions.toPlane (1 : ℂ) := by
  unfold rightCenterPlane TDCSG.Definitions.toPlane
  ext i
  fin_cases i <;> simp [Complex.one_re, Complex.one_im]

/-- DEPRECATED: leftCenter is now ℂ, equal to -1. -/
lemma leftCenter_eq_neg_one : leftCenter = (-1 : ℂ) := rfl

/-- DEPRECATED: rightCenter is now ℂ, equal to 1. -/
lemma rightCenter_eq_one : rightCenter = (1 : ℂ) := rfl

/-- Segment points are in the left disk at r_crit. -/
lemma segmentPointPlane_in_leftDisk (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    TDCSG.Definitions.segmentPointPlane t ∈ leftDiskPlane r_crit := by
  unfold leftDiskPlane closedDisk
  rw [Metric.mem_closedBall]
  rw [leftCenterPlane_eq_toPlane]
  unfold TDCSG.Definitions.segmentPointPlane
  rw [toPlane_dist_eq_complex_norm]
  rw [show TDCSG.Definitions.segmentPoint t - (-1 : ℂ) = TDCSG.Definitions.segmentPoint t + 1 by ring]
  have h_mem := segment_in_disk_intersection t ⟨ht.1, le_of_lt ht.2⟩
  unfold TDCSG.Definitions.segmentPoint at h_mem ⊢
  exact h_mem.1

/-- Segment points are in the right disk at r_crit. -/
lemma segmentPointPlane_in_rightDisk (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    TDCSG.Definitions.segmentPointPlane t ∈ rightDiskPlane r_crit := by
  unfold rightDiskPlane closedDisk
  rw [Metric.mem_closedBall]
  rw [rightCenterPlane_eq_toPlane]
  unfold TDCSG.Definitions.segmentPointPlane
  rw [toPlane_dist_eq_complex_norm]
  rw [show TDCSG.Definitions.segmentPoint t - (1 : ℂ) = TDCSG.Definitions.segmentPoint t - 1 by ring]
  have h_mem := segment_in_disk_intersection t ⟨ht.1, le_of_lt ht.2⟩
  unfold TDCSG.Definitions.segmentPoint at h_mem ⊢
  exact h_mem.2

/-! ### Generator actions in terms of complex multiplication

With the clockwise convention:
- genA/genB use ζ₅⁴ = exp(-2πi/5) for forward rotation
- A⁻¹ = A⁴ uses (ζ₅⁴)⁴ = ζ₅¹⁶ = ζ₅ for inverse rotation
-/

/-- genAPlane on a point in the left disk equals rotation by ζ₅⁴ about -1 in complex coords (clockwise). -/
lemma genAPlane_eq_zeta5_pow4_rotation (z : ℂ) (hz : TDCSG.Definitions.toPlane z ∈ leftDiskPlane r_crit) :
    genAPlane r_crit (TDCSG.Definitions.toPlane z) = TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^4 * (z - (-1))) := by
  unfold genAPlane
  rw [if_pos hz]
  rw [leftCenterPlane_eq_toPlane]
  exact (zeta5_pow4_rotation_eq_rotateAroundPoint z (-1)).symm

/-- genBPlane on a point in the right disk equals rotation by ζ₅⁴ about 1 in complex coords (clockwise). -/
lemma genBPlane_eq_zeta5_pow4_rotation (z : ℂ) (hz : TDCSG.Definitions.toPlane z ∈ rightDiskPlane r_crit) :
    genBPlane r_crit (TDCSG.Definitions.toPlane z) = TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^4 * (z - 1)) := by
  unfold genBPlane
  rw [if_pos hz]
  rw [rightCenterPlane_eq_toPlane]
  exact (zeta5_pow4_rotation_eq_rotateAroundPoint z 1).symm

/-- The rotation angle 2π/5 in exponential form equals ζ₅. -/
lemma exp_form_eq_zeta5 : Complex.exp (↑(2 * Real.pi / 5) * I) = ζ₅ := by
  unfold ζ₅ zeta5
  congr 1
  push_cast
  ring

/-- The rotation angle -2π/5 in exponential form equals ζ₅⁴. -/
lemma exp_neg_form_eq_zeta5_pow4 : Complex.exp (↑(-2 * Real.pi / 5) * I) = ζ₅^4 := by
  rw [zeta5_inv_as_pow4.symm]
  unfold ζ₅ zeta5
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- genA on ℂ equals rotation by ζ₅⁴ about -1 (clockwise convention). -/
lemma genA_eq_zeta5_pow4_rotation (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    genA r_crit z = (-1 : ℂ) + ζ₅^4 * (z - (-1)) := by
  unfold genA
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC leftCenter
  rw [exp_neg_form_eq_zeta5_pow4]

/-- genB on ℂ equals rotation by ζ₅⁴ about 1 (clockwise convention). -/
lemma genB_eq_zeta5_pow4_rotation (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    genB r_crit z = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold genB
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC rightCenter
  rw [exp_neg_form_eq_zeta5_pow4]

/-- A⁻¹ = A⁴ means multiplying by ζ₅ (ℂ version, clockwise convention).
    Since forward A uses ζ₅⁴, applying A four times gives (ζ₅⁴)⁴ = ζ₅¹⁶ = ζ₅. -/
lemma genA_inv_eq_zeta5_rotation (z : ℂ)
    (hz : z ∈ leftDisk r_crit)
    (hz' : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit)
    (hz'' : (-1 : ℂ) + ζ₅^3 * (z + 1) ∈ leftDisk r_crit)
    (hz''' : (-1 : ℂ) + ζ₅^2 * (z + 1) ∈ leftDisk r_crit) :
    genA r_crit (genA r_crit (genA r_crit (genA r_crit z))) =
    (-1 : ℂ) + ζ₅ * (z + 1) := by
  rw [genA_eq_zeta5_pow4_rotation z hz]
  rw [show -1 + ζ₅^4 * (z - -1) = -1 + ζ₅^4 * (z + 1) by ring]
  rw [genA_eq_zeta5_pow4_rotation _ hz']
  rw [show -1 + ζ₅^4 * (-1 + ζ₅^4 * (z + 1) - -1) = -1 + ζ₅^3 * (z + 1) by
    have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
    ring_nf; rw [h8]]
  rw [genA_eq_zeta5_pow4_rotation _ hz'']
  rw [show -1 + ζ₅^4 * (-1 + ζ₅^3 * (z + 1) - -1) = -1 + ζ₅^2 * (z + 1) by
    have h7 : ζ₅^7 = ζ₅^2 := zeta5_pow_seven
    ring_nf; rw [h7]]
  rw [genA_eq_zeta5_pow4_rotation _ hz''']
  rw [show -1 + ζ₅^4 * (-1 + ζ₅^2 * (z + 1) - -1) = -1 + ζ₅ * (z + 1) by
    have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
    ring_nf; rw [h6]]

/-- B⁻¹ = B⁴ means multiplying by ζ₅ (ℂ version, clockwise convention).
    Since forward B uses ζ₅⁴, applying B four times gives (ζ₅⁴)⁴ = ζ₅¹⁶ = ζ₅. -/
lemma genB_inv_eq_zeta5_rotation (z : ℂ)
    (hz : z ∈ rightDisk r_crit)
    (hz' : (1 : ℂ) + ζ₅^4 * (z - 1) ∈ rightDisk r_crit)
    (hz'' : (1 : ℂ) + ζ₅^3 * (z - 1) ∈ rightDisk r_crit)
    (hz''' : (1 : ℂ) + ζ₅^2 * (z - 1) ∈ rightDisk r_crit) :
    genB r_crit (genB r_crit (genB r_crit (genB r_crit z))) =
    (1 : ℂ) + ζ₅ * (z - 1) := by
  rw [genB_eq_zeta5_pow4_rotation z hz]
  rw [genB_eq_zeta5_pow4_rotation _ hz']
  rw [show 1 + ζ₅^4 * (1 + ζ₅^4 * (z - 1) - 1) = 1 + ζ₅^3 * (z - 1) by
    have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
    ring_nf; rw [h8]]
  rw [genB_eq_zeta5_pow4_rotation _ hz'']
  rw [show 1 + ζ₅^4 * (1 + ζ₅^3 * (z - 1) - 1) = 1 + ζ₅^2 * (z - 1) by
    have h7 : ζ₅^7 = ζ₅^2 := zeta5_pow_seven
    ring_nf; rw [h7]]
  rw [genB_eq_zeta5_pow4_rotation _ hz''']
  rw [show 1 + ζ₅^4 * (1 + ζ₅^2 * (z - 1) - 1) = 1 + ζ₅ * (z - 1) by
    have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
    ring_nf; rw [h6]]

/-- A⁻¹ = A⁴ means multiplying by ζ₅ (Plane version, clockwise convention).
    Since forward uses ζ₅⁴, applying 4 times gives (ζ₅⁴)⁴ = ζ₅. -/
lemma genAPlane_inv_eq_zeta5_rotation (z : ℂ)
    (hz : TDCSG.Definitions.toPlane z ∈ leftDiskPlane r_crit)
    (hz' : TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^4 * (z + 1)) ∈ leftDiskPlane r_crit)
    (hz'' : TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^3 * (z + 1)) ∈ leftDiskPlane r_crit)
    (hz''' : TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^2 * (z + 1)) ∈ leftDiskPlane r_crit) :
    genAPlane r_crit (genAPlane r_crit (genAPlane r_crit
      (genAPlane r_crit (TDCSG.Definitions.toPlane z)))) =
    TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅ * (z + 1)) := by
  rw [genAPlane_eq_zeta5_pow4_rotation z hz]
  rw [show -1 + ζ₅^4 * (z - -1) = -1 + ζ₅^4 * (z + 1) by ring]
  rw [genAPlane_eq_zeta5_pow4_rotation _ hz']
  rw [show -1 + ζ₅^4 * (-1 + ζ₅^4 * (z + 1) - -1) = -1 + ζ₅^3 * (z + 1) by
    have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
    ring_nf; rw [h8]]
  rw [genAPlane_eq_zeta5_pow4_rotation _ hz'']
  rw [show -1 + ζ₅^4 * (-1 + ζ₅^3 * (z + 1) - -1) = -1 + ζ₅^2 * (z + 1) by
    have h7 : ζ₅^7 = ζ₅^2 := zeta5_pow_seven
    ring_nf; rw [h7]]
  rw [genAPlane_eq_zeta5_pow4_rotation _ hz''']
  rw [show -1 + ζ₅^4 * (-1 + ζ₅^2 * (z + 1) - -1) = -1 + ζ₅ * (z + 1) by
    have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
    ring_nf; rw [h6]]

/-- B⁻¹ = B⁴ means multiplying by ζ₅ (Plane version, clockwise convention).
    Since forward uses ζ₅⁴, applying 4 times gives (ζ₅⁴)⁴ = ζ₅. -/
lemma genBPlane_inv_eq_zeta5_rotation (z : ℂ)
    (hz : TDCSG.Definitions.toPlane z ∈ rightDiskPlane r_crit)
    (hz' : TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^4 * (z - 1)) ∈ rightDiskPlane r_crit)
    (hz'' : TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^3 * (z - 1)) ∈ rightDiskPlane r_crit)
    (hz''' : TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^2 * (z - 1)) ∈ rightDiskPlane r_crit) :
    genBPlane r_crit (genBPlane r_crit (genBPlane r_crit
      (genBPlane r_crit (TDCSG.Definitions.toPlane z)))) =
    TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅ * (z - 1)) := by
  rw [genBPlane_eq_zeta5_pow4_rotation z hz]
  rw [genBPlane_eq_zeta5_pow4_rotation _ hz']
  rw [show 1 + ζ₅^4 * (1 + ζ₅^4 * (z - 1) - 1) = 1 + ζ₅^3 * (z - 1) by
    have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
    ring_nf; rw [h8]]
  rw [genBPlane_eq_zeta5_pow4_rotation _ hz'']
  rw [show 1 + ζ₅^4 * (1 + ζ₅^3 * (z - 1) - 1) = 1 + ζ₅^2 * (z - 1) by
    have h7 : ζ₅^7 = ζ₅^2 := zeta5_pow_seven
    ring_nf; rw [h7]]
  rw [genBPlane_eq_zeta5_pow4_rotation _ hz''']
  rw [show 1 + ζ₅^4 * (1 + ζ₅^2 * (z - 1) - 1) = 1 + ζ₅ * (z - 1) by
    have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
    ring_nf; rw [h6]]

end TDCSG.CompoundSymmetry.GG5
