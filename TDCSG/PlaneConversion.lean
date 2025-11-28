/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Conversions
import TDCSG.Definitions.Geometry
import TDCSG.Definitions.Core
import TDCSG.Points
import TDCSG.MainTheorem

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
* `zeta5_rotation_eq_rotateAround` : ζ₅ multiplication corresponds to rotation
* `genA_eq_zeta5_rotation` : genA equals ζ₅ rotation about -1
* `genB_eq_zeta5_rotation` : genB equals ζ₅ rotation about 1

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

/-- Compute real part of E -/
private lemma E_re : E.re = Real.cos (2 * π / 5) - Real.cos (4 * π / 5) := by
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

/-- Trigonometric identity: cos(4*pi/5) = -cos(pi/5) -/
private lemma cos_four_pi_fifth : Real.cos (4 * π / 5) = -Real.cos (π / 5) := by
  rw [show (4 * π / 5 : ℝ) = π - π / 5 by ring, Real.cos_pi_sub]

/-- Point E has positive real part.
This is a computationally verifiable fact using E = ζ₅ - ζ₅². -/
lemma E_re_pos : 0 < E.re := by
  rw [E_re, cos_four_pi_fifth, cos_two_pi_fifth, Real.cos_pi_div_five]
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

/-- Rotation in ℂ by ζ₅ corresponds to rotateAround in Plane.

This is the key lemma connecting complex multiplication to plane rotation:
- In ℂ: rotation around c by 2π/5 maps z to c + ζ₅ * (z - c)
- In Plane: rotateAround center (2π/5) p uses the rotation matrix
Both are equivalent when we identify ℂ with ℝ² via toPlane/fromPlane.

The proof follows from:
1. ζ₅ = exp(2πi/5) = cos(2π/5) + i·sin(2π/5)
2. Complex multiplication by ζ₅ is rotation in ℝ²
3. The rotation matrix [[cos θ, -sin θ], [sin θ, cos θ]] acts identically -/
theorem zeta5_rotation_eq_rotateAround (z c : ℂ) :
    TDCSG.Definitions.toPlane (c + ζ₅ * (z - c)) = rotateAround (TDCSG.Definitions.toPlane c) (2 * π / 5) (TDCSG.Definitions.toPlane z) := by
  -- Unfold rotateAround definition
  unfold rotateAround
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

/-! ### Segment parameterization -/

-- Note: segmentPoint, segmentPointPlane, segmentPoint_eq_scalar_E, segmentPoint_translate
-- are defined in TDCSG.Definitions.Conversions

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

/-- leftCenter equals toPlane (-1). -/
lemma leftCenter_eq_toPlane : leftCenter = TDCSG.Definitions.toPlane (-1 : ℂ) := by
  unfold leftCenter TDCSG.Definitions.toPlane
  ext i
  fin_cases i <;> simp [Complex.neg_re, Complex.neg_im]

/-- rightCenter equals toPlane (1). -/
lemma rightCenter_eq_toPlane : rightCenter = TDCSG.Definitions.toPlane (1 : ℂ) := by
  unfold rightCenter TDCSG.Definitions.toPlane
  ext i
  fin_cases i <;> simp [Complex.one_re, Complex.one_im]

/-- Segment points are in the left disk at r_crit. -/
lemma segmentPointPlane_in_leftDisk (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    TDCSG.Definitions.segmentPointPlane t ∈ leftDisk r_crit := by
  unfold leftDisk closedDisk
  rw [Metric.mem_closedBall]
  rw [leftCenter_eq_toPlane]
  unfold TDCSG.Definitions.segmentPointPlane
  rw [toPlane_dist_eq_complex_norm]
  rw [show TDCSG.Definitions.segmentPoint t - (-1 : ℂ) = TDCSG.Definitions.segmentPoint t + 1 by ring]
  have h_mem := segment_in_disk_intersection t ⟨ht.1, le_of_lt ht.2⟩
  unfold TDCSG.Definitions.segmentPoint at h_mem ⊢
  exact h_mem.1

/-- Segment points are in the right disk at r_crit. -/
lemma segmentPointPlane_in_rightDisk (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    TDCSG.Definitions.segmentPointPlane t ∈ rightDisk r_crit := by
  unfold rightDisk closedDisk
  rw [Metric.mem_closedBall]
  rw [rightCenter_eq_toPlane]
  unfold TDCSG.Definitions.segmentPointPlane
  rw [toPlane_dist_eq_complex_norm]
  rw [show TDCSG.Definitions.segmentPoint t - (1 : ℂ) = TDCSG.Definitions.segmentPoint t - 1 by ring]
  have h_mem := segment_in_disk_intersection t ⟨ht.1, le_of_lt ht.2⟩
  unfold TDCSG.Definitions.segmentPoint at h_mem ⊢
  exact h_mem.2

/-! ### Generator actions in terms of complex multiplication -/

/-- genA on a point in the left disk equals rotation by ζ₅ about -1 in complex coords. -/
lemma genA_eq_zeta5_rotation (z : ℂ) (hz : TDCSG.Definitions.toPlane z ∈ leftDisk r_crit) :
    genA r_crit (TDCSG.Definitions.toPlane z) = TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅ * (z - (-1))) := by
  unfold genA
  rw [if_pos hz]
  rw [leftCenter_eq_toPlane]
  exact (zeta5_rotation_eq_rotateAround z (-1)).symm

/-- genB on a point in the right disk equals rotation by ζ₅ about 1 in complex coords. -/
lemma genB_eq_zeta5_rotation (z : ℂ) (hz : TDCSG.Definitions.toPlane z ∈ rightDisk r_crit) :
    genB r_crit (TDCSG.Definitions.toPlane z) = TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅ * (z - 1)) := by
  unfold genB
  rw [if_pos hz]
  rw [rightCenter_eq_toPlane]
  exact (zeta5_rotation_eq_rotateAround z 1).symm

/-- A⁻¹ = A⁴ means multiplying by ζ₅⁴. -/
lemma genA_inv_eq_zeta5_pow4_rotation (z : ℂ)
    (hz : TDCSG.Definitions.toPlane z ∈ leftDisk r_crit)
    (hz' : TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅ * (z + 1)) ∈ leftDisk r_crit)
    (hz'' : TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^2 * (z + 1)) ∈ leftDisk r_crit)
    (hz''' : TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^3 * (z + 1)) ∈ leftDisk r_crit) :
    genA r_crit (genA r_crit (genA r_crit
      (genA r_crit (TDCSG.Definitions.toPlane z)))) =
    TDCSG.Definitions.toPlane ((-1 : ℂ) + ζ₅^4 * (z + 1)) := by
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
    (hz : TDCSG.Definitions.toPlane z ∈ rightDisk r_crit)
    (hz' : TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅ * (z - 1)) ∈ rightDisk r_crit)
    (hz'' : TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^2 * (z - 1)) ∈ rightDisk r_crit)
    (hz''' : TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^3 * (z - 1)) ∈ rightDisk r_crit) :
    genB r_crit (genB r_crit (genB r_crit
      (genB r_crit (TDCSG.Definitions.toPlane z)))) =
    TDCSG.Definitions.toPlane ((1 : ℂ) + ζ₅^4 * (z - 1)) := by
  rw [genB_eq_zeta5_rotation z hz]
  rw [genB_eq_zeta5_rotation _ hz']
  rw [show 1 + ζ₅ * (1 + ζ₅ * (z - 1) - 1) = 1 + ζ₅^2 * (z - 1) by ring]
  rw [genB_eq_zeta5_rotation _ hz'']
  rw [show 1 + ζ₅ * (1 + ζ₅ ^ 2 * (z - 1) - 1) = 1 + ζ₅^3 * (z - 1) by ring]
  rw [genB_eq_zeta5_rotation _ hz''']
  rw [show 1 + ζ₅ * (1 + ζ₅ ^ 3 * (z - 1) - 1) = 1 + ζ₅^4 * (z - 1) by ring]

end TDCSG.CompoundSymmetry.GG5
