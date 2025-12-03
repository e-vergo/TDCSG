/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.Points
import TDCSG.Definitions.GroupAction

/-!
# Segment Geometry

This file proves geometric properties of the segment connecting E' and E, establishing that it
lies in the intersection of both disks and that the segment parameterization is injective.

## Main results

- `segmentPoint_injective`: The segment parameterization is injective
- `E'_on_right_disk_boundary`: Point E' lies on the boundary of the right disk
- `E'_in_left_disk`: Point E' lies inside the left disk
- `segment_in_disk_intersection`: The segment lies in both disks

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions (segmentPoint E E' ζ₅ φ r_crit)

/-- The point `E = zeta5^4 - zeta5^3` is nonzero.

This is a foundational fact needed for the injectivity of the segment parameterization.
The proof proceeds by contradiction: if `E = 0`, then `zeta5^3 * (zeta5 - 1) = 0`, which
would imply either `zeta5^3 = 0` (impossible since `zeta5` is a root of unity) or
`zeta5 = 1` (contradicting that `zeta5` is a primitive 5th root of unity). -/
lemma E_ne_zero : E ≠ 0 := by

  intro h
  unfold E at h
  have h2 : ζ₅^3 * (ζ₅ - 1) = 0 := by
    calc ζ₅^3 * (ζ₅ - 1) = ζ₅^4 - ζ₅^3 := by ring
                     _ = 0 := h
  have h3 : ζ₅^3 ≠ 0 := by
    intro h0
    have : (0 : ℂ) ^ 5 = 1 := by
      have h3_pow : (ζ₅^3)^5 = 1 := by
        calc (ζ₅^3)^5 = ζ₅^15 := by ring
          _ = (ζ₅^5)^3 := by ring
          _ = 1^3 := by rw [zeta5_pow_five]
          _ = 1 := by ring
      calc (0 : ℂ) ^ 5 = (ζ₅^3) ^ 5 := by rw [← h0]
                     _ = 1 := h3_pow
    norm_num at this
  have h4 : ζ₅ - 1 = 0 := by
    exact (mul_eq_zero.mp h2).resolve_left h3
  have : ζ₅ = 1 := by
    have h5 : 1 = ζ₅ := by
      calc 1 = 0 + 1 := by simp
           _ = (ζ₅ - 1) + 1 := by rw [← h4]
           _ = ζ₅ := by ring
    exact h5.symm
  exact zeta5_ne_one this

/-- The segment parameterization `segmentPoint : R -> C` given by `t |-> E' + t * (E - E')` is
injective.

This establishes that the line segment from E' to E has no self-intersections when parameterized
by the real line. The proof uses that `E - E' = 2E` is nonzero (from `E_ne_zero`), so the
parameterization is a non-degenerate affine map.

This injectivity is crucial for the dynamical argument in the paper showing that GG_5 is infinite
at the critical radius: the three piecewise transformations translate portions of segment E'E
onto itself, and injectivity ensures distinct parameter values map to distinct points. -/
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

  by_contra h_ne
  have : t₁ • (E - E') - t₂ • (E - E') = 0 := by
    rw [this]; ring
  rw [← sub_smul] at this
  have hsub_ne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have : E - E' = 0 := by
    have h_smul : (t₁ - t₂) • (E - E') = 0 := this
    exact smul_eq_zero.mp h_smul |>.resolve_left hsub_ne
  exact hne this

/-- Point E' lies exactly on the boundary of the right disk (centered at 1 with radius `r_crit`).

Since `E' = -E` by definition, and the two-disk system is symmetric about the origin,
E' being on the right disk boundary is equivalent to E being on the left disk boundary
(proved in `E_on_left_disk_boundary`). This symmetry is essential: together with
`E_on_left_disk_boundary`, it shows that the segment E'E has its endpoints on opposite
disk boundaries, spanning the disk intersection region. -/
lemma E'_on_right_disk_boundary : ‖E' - 1‖ = r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (1 : ℂ)) = -(E + 1) by ring]
  rw [norm_neg]
  exact E_on_left_disk_boundary

/-- Point E' lies inside (or on the boundary of) the left disk (centered at -1 with radius `r_crit`).

By symmetry, `E' = -E` being in the left disk is equivalent to E being in the right disk.
Combined with `E'_on_right_disk_boundary`, this shows E' lies in the intersection of both disks,
which is the "active region" where both rotations can act on points. -/
lemma E'_in_left_disk : ‖E' - (-1)‖ ≤ r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (-1 : ℂ)) = -(E - 1) by ring]
  rw [norm_neg]
  exact E_in_right_disk

/-- Every point on the segment from E' to E lies in the intersection of both disks.

For any parameter `t` in [0,1], the point `p = E' + t * (E - E')` satisfies both
`|p + 1| <= r_crit` (inside left disk) and `|p - 1| <= r_crit` (inside right disk).

This is the key geometric containment result for the GG_5 critical radius proof. The paper's
dynamical argument shows that certain group element sequences translate portions of this
segment onto itself without any point ever leaving the disk intersection. This lemma provides
the necessary containment guarantee: if a point starts on the segment, and the segment is
contained in the disk intersection, then the transformations (which preserve points in their
respective disks) keep the point in the active region where both rotations can act.

The proof uses convexity of closed balls: since both E' and E lie in each disk (by
`E'_in_left_disk`, `E_on_left_disk_boundary`, `E'_on_right_disk_boundary`, `E_in_right_disk`),
and closed balls are convex, the entire segment lies in each disk. -/
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

end TDCSG.CompoundSymmetry.GG5
