/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Geometry
import TDCSG.Proofs.SegmentGeometry

/-!
# Disk Intersection and Segment Parameterization for GG(5,5)

Proofs about disk membership, segment parameterization, and generator rotation formulas.

The conversion definitions are in TDCSG.Definitions.Conversions.

## Main Results

### Disk Intersection
* `E'_on_right_disk_boundary` : E' is on the right disk boundary
* `E'_in_left_disk` : E' is in the left disk
* `segment_in_disk_intersection` : Points on segment E'E lie in both disks

### Segment Parameterization
* `segmentPoint_injective` : The segment parameterization is injective

### Generator Rotation Formulas (ℂ-native)
* `genA_eq_zeta5_pow4_rotation` : genA equals ζ₅⁴ rotation about -1 (clockwise)
* `genB_eq_zeta5_pow4_rotation` : genB equals ζ₅⁴ rotation about 1 (clockwise)
* `genA_inv_eq_zeta5_rotation` : A⁻¹ = A⁴ uses ζ₅ rotation
* `genB_inv_eq_zeta5_rotation` : B⁻¹ = B⁴ uses ζ₅ rotation

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

/-! ### Generator actions in terms of complex multiplication

With the clockwise convention:
- genA/genB use ζ₅⁴ = exp(-2πi/5) for forward rotation
- A⁻¹ = A⁴ uses (ζ₅⁴)⁴ = ζ₅¹⁶ = ζ₅ for inverse rotation
-/

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

end TDCSG.CompoundSymmetry.GG5
