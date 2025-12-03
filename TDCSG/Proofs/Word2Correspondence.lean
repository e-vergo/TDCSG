/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.CrossDiskWord2DiskBounds

/-!
# Word 2 Correspondence for GG_5

This file establishes the correspondence between the word `a^{-1}b^{-1}a^{-1}b^{-2}` (word2)
and the Interval Exchange Transformation (IET) dynamics for the second interval of the
GG_5 compound symmetry group at critical radius.

## Mathematical Context

In the paper "Two-Disk Compound Symmetry Groups", the proof that GG_5 is infinite at
critical radius r = sqrt(3 + phi) proceeds by showing that points along the segment E'E
can be translated piecewise onto itself indefinitely. The segment is partitioned into
three intervals, and each interval has an associated "word" (group element) that
translates points within that interval.

For interval 1 (points with parameter x in [length1, length1 + length2)):
- The associated word is `a^{-1}b^{-1}a^{-1}b^{-2}` (encoded as word2)
- Applying this word produces a translation by displacement1 along E'E
- The ratio of interval lengths involves the golden ratio, ensuring the dynamics
  are non-periodic

## Main Results

- `word2_produces_displacement1`: For points in interval 1 of the IET partition,
  applying word2 translates them by exactly displacement1 along the segment E'E.

## Implementation Notes

The proof proceeds by:
1. Computing the parametrized point z0 = c * E where c = 2x - 1
2. Verifying that each intermediate point z1, z2, z3, z4, z5 in the word application
   remains within the appropriate disk (so the rotations are well-defined)
3. Using the algebraic identity from `AlgebraicIdentities.lean` to conclude that
   z5 = z0 + (2 * displacement1) * E

## References

* Main paper: "Two-Disk Compound Symmetry Groups" (Hearn, Kretschmer, Rokicki, Streeter, Vergo)
* See Theorem 2 in the paper for the geometric construction
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions

/-- Applying word2 to points in interval 1 produces a translation by displacement1.

This lemma is one of three correspondence lemmas (for words 1, 2, and 3) that together
establish the piecewise translation structure used to prove GG_5 is infinite at
critical radius.

**Mathematical content**: For x in [length1, length1 + length2), the point
`segmentPoint x` lies on the segment E'E. Applying the word `a^{-1}b^{-1}a^{-1}b^{-2}`
(equivalently, rotating by zeta_5 about the appropriate centers in sequence) translates
this point to `segmentPoint (x + displacement1)`.

**Geometric interpretation**: This corresponds to case (1) in the paper's proof of
Theorem 2, where the line segment E'F' is transformed by `a^{-2}b^{-1}a^{-1}b^{-1}`
to line segment GF. The translation length is |F - F'|.

The proof verifies that all intermediate points z1, z2, z3, z4 during the word
application remain within the appropriate disks, ensuring each rotation step is
well-defined. The disk membership bounds come from `CrossDiskWord2DiskBounds.lean`. -/
lemma word2_produces_displacement1 (x : ℝ) (hx : x ∈ Set.Ico 0 1)
    (hx_lo : length1 ≤ x) (hx_hi : x < length1 + length2) :
    applyWord r_crit word2 (segmentPoint x) =
    segmentPoint (x + displacement1) := by

  rw [segmentPoint_add_displacement]

  set c := 2 * x - 1 with hc_def
  have hc_lo : -1 ≤ c := by simp only [hc_def]; linarith [hx.1]
  have hc_hi_le : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨hc_lo, hc_hi_le⟩

  have hc_interval_lo : (1 - √5) / 2 ≤ c := interval1_c_lower_bound x hx_lo
  have hc_interval_hi : c < 2 - √5 := interval1_c_upper_bound x hx_hi
  have hc_interval_hi_le : c ≤ 2 - √5 := le_of_lt hc_interval_hi

  have h_z0_eq : segmentPoint x = (c : ℂ) • E := by
    rw [segmentPoint_eq_smul_E, hc_def]
    simp only [Complex.real_smul, smul_eq_mul]

  have h_in_disks := segment_in_disk_intersection x ⟨hx.1, le_of_lt hx.2⟩
  have hz0_left : segmentPoint x ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    rw [show segmentPoint x - (-1 : ℂ) = segmentPoint x + 1 by ring]
    unfold segmentPoint
    exact h_in_disks.1
  have hz0_right : segmentPoint x ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    unfold segmentPoint
    exact h_in_disks.2

  have h_alg := word2_algebraic_identity c h_c_mem
  simp only at h_alg

  unfold applyWord word2
  simp only [List.foldl_cons, List.foldl_nil]

  rw [h_z0_eq]

  let z0 : ℂ := (c : ℂ) • E
  let z1 := (-1 : ℂ) + ζ₅ * (z0 + 1)
  let z2 := (1 : ℂ) + ζ₅ * (z1 - 1)
  let z3 := (-1 : ℂ) + ζ₅ * (z2 + 1)
  let z4 := (1 : ℂ) + ζ₅ * (z3 - 1)
  let z5 := (1 : ℂ) + ζ₅ * (z4 - 1)

  have h_z5_eq : z5 = z0 + (2 * displacement1) • E := by
    simp only [z5, z4, z3, z2, z1, z0]
    convert h_alg using 1

  have hz0_left' : z0 ∈ leftDisk r_crit := by
    simp only [z0]
    rw [show (c : ℂ) • E = segmentPoint x by rw [h_z0_eq]]
    exact hz0_left
  have hz0_right' : z0 ∈ rightDisk r_crit := by
    simp only [z0]
    rw [show (c : ℂ) • E = segmentPoint x by rw [h_z0_eq]]
    exact hz0_right

  suffices h : applyGen r_crit
      (applyGen r_crit
        (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv)
          .Ainv)
        .Binv)
      .Binv = z5 by
    rw [h, h_z5_eq]

  have hz1_left : z1 ∈ leftDisk r_crit := by
    simp only [z1]
    have h := leftDisk_zeta_rotation r_crit 1 z0 hz0_left'
    simpa using h

  have hz1_right : z1 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]

    have h_z1_minus_1 : z1 - 1 = starRingEnd ℂ ((ζ₅^4 - 2 : ℂ) + (c : ℂ) * (1 - ζ₅)) := by
      simp only [z1, z0, E]
      rw [smul_eq_mul]
      have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_pow, zeta5_conj, map_one]
      ring_nf
      simp only [zeta5_pow_five, zeta5_pow_sixteen, hconj2]
      ring
    rw [h_z1_minus_1, Complex.norm_conj]
    exact cross_disk_w2_z1_bound c hc_interval_lo hc_interval_hi_le

  have hz2_right : z2 ∈ rightDisk r_crit := by
    simp only [z2]
    have h := rightDisk_zeta_rotation r_crit 1 z1 hz1_right
    simpa using h

  have hz2_left : z2 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z2_plus_1 : z2 + 1 = starRingEnd ℂ (((2 : ℂ) - 2*ζ₅^4 + ζ₅^3) + (c : ℂ) * (ζ₅^4 - 1)) := by
      simp only [z2, z1, z0, E]
      rw [smul_eq_mul]
      have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_pow, zeta5_conj, map_one]
      ring_nf
      simp only [zeta5_pow_five, zeta5_pow_six, zeta5_pow_twelve, zeta5_pow_sixteen, hconj2]
      ring
    rw [show z2 - (-1 : ℂ) = z2 + 1 by ring, h_z2_plus_1, Complex.norm_conj]
    exact cross_disk_w2_z2_bound c hc_interval_lo hc_interval_hi_le

  have hz3_left : z3 ∈ leftDisk r_crit := by
    simp only [z3]
    have h := leftDisk_zeta_rotation r_crit 1 z2 hz2_left
    simpa using h

  have hz3_right : z3 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z3_minus_1 : z3 - 1 = starRingEnd ℂ (((-2 : ℂ) + 2*ζ₅^4 - 2*ζ₅^3 + ζ₅^2) + (c : ℂ) * (ζ₅^3 - ζ₅^4)) := by
      simp only [z3, z2, z1, z0, E]
      rw [smul_eq_mul]
      have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_pow, zeta5_conj, map_neg]
      ring_nf
      simp only [zeta5_pow_six, zeta5_pow_seven, zeta5_pow_eight, zeta5_pow_twelve,
        zeta5_pow_sixteen, hconj2]
      ring
    rw [h_z3_minus_1, Complex.norm_conj]
    exact cross_disk_w2_z3_bound c hc_interval_lo hc_interval_hi_le

  have hz4_right : z4 ∈ rightDisk r_crit := by
    simp only [z4]
    have h := rightDisk_zeta_rotation r_crit 1 z3 hz3_right
    simpa using h

  have h_step1 : applyGen r_crit z0 .Ainv = z1 := applyGen_Ainv_formula' z0 hz0_left'
  have h_step2 : applyGen r_crit z1 .Binv = z2 := applyGen_Binv_formula' z1 hz1_right
  have h_step3 : applyGen r_crit z2 .Ainv = z3 := applyGen_Ainv_formula' z2 hz2_left
  have h_step4 : applyGen r_crit z3 .Binv = z4 := applyGen_Binv_formula' z3 hz3_right
  have h_step5 : applyGen r_crit z4 .Binv = z5 := applyGen_Binv_formula' z4 hz4_right

  calc applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv) .Ainv) .Binv) .Binv
      = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z1 .Binv) .Ainv) .Binv) .Binv := by rw [h_step1]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit z2 .Ainv) .Binv) .Binv := by rw [h_step2]
    _ = applyGen r_crit (applyGen r_crit z3 .Binv) .Binv := by rw [h_step3]
    _ = applyGen r_crit z4 .Binv := by rw [h_step4]
    _ = z5 := h_step5

end TDCSG.CompoundSymmetry.GG5
