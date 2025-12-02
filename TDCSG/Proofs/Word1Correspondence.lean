/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.CrossDiskRestricted

/-!
# Word 1 Correspondence

This file proves that applying word1 to points in the first IET interval produces the correct
displacement, establishing the correspondence between the IET and group action for interval 0.

## Main results

- `interval0_c_upper_bound`: Points in interval 0 satisfy an upper bound
- `word1_produces_displacement0`: Word1 produces displacement0 for interval 0 points

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions

lemma interval0_c_upper_bound (x : ℝ) (hx : x < length1) :
    2 * x - 1 < (1 - Real.sqrt 5) / 2 := by
  have h_phi := Real.goldenRatio.eq_1
  have h_two_length1 : 2 * length1 = 2 / (3 + Real.sqrt 5) := by
    unfold length1
    rw [h_phi]
    field_simp
    ring
  have h_target : 2 * length1 - 1 = (1 - Real.sqrt 5) / 2 := by
    rw [h_two_length1]
    have h_denom_pos : 3 + Real.sqrt 5 > 0 := by
      have h_sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
      linarith
    have h_denom_ne : 3 + Real.sqrt 5 ≠ 0 := ne_of_gt h_denom_pos
    field_simp
    nlinarith [sqrt5_sq]
  grind

lemma word1_produces_displacement0 (x : ℝ) (hx : x ∈ Set.Ico 0 1) (hx_int : x < length1) :
    applyWord r_crit word1 (segmentPoint x) =
    segmentPoint (x + displacement0) := by

  rw [segmentPoint_add_displacement]

  set c := 2 * x - 1 with hc_def
  have hc_lo : -1 ≤ c := by simp only [hc_def]; linarith [hx.1]
  have hc_hi_le : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨hc_lo, hc_hi_le⟩

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

  have h_alg := word1_algebraic_identity c h_c_mem
  simp only at h_alg

  unfold applyWord word1
  simp only [List.foldl_cons, List.foldl_nil]

  rw [h_z0_eq]

  let z0 : ℂ := (c : ℂ) • E
  let z1 := (-1 : ℂ) + ζ₅^4 * (z0 + 1)
  let z2 := (-1 : ℂ) + ζ₅^4 * (z1 + 1)
  let z3 := (1 : ℂ) + ζ₅^4 * (z2 - 1)
  let z4 := (-1 : ℂ) + ζ₅^4 * (z3 + 1)
  let z5 := (1 : ℂ) + ζ₅^4 * (z4 - 1)

  have h_z5_eq : z5 = z0 + (2 * displacement0) • E := by
    simp only [z5, z4, z3, z2, z1, z0]
    convert h_alg using 1

  have hc_hi : c < (1 - Real.sqrt 5) / 2 := interval0_c_upper_bound x hx_int
  have hc_hi_le' : c ≤ (1 - Real.sqrt 5) / 2 := le_of_lt hc_hi

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
        (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .A) .A) .B)
        .A)
      .B = z5 by
    rw [h, h_z5_eq]

  have hz1_left : z1 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_left' ⊢
    simp only [Set.mem_setOf_eq] at hz0_left' ⊢
    simp only [z1]
    rw [show (-1 : ℂ) + ζ₅^4 * (z0 + 1) - (-1) = ζ₅^4 * (z0 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    grind

  have hz2_left : z2 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz1_left ⊢
    simp only [Set.mem_setOf_eq] at hz1_left ⊢
    simp only [z2]
    rw [show (-1 : ℂ) + ζ₅^4 * (z1 + 1) - (-1) = ζ₅^4 * (z1 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    grind

  have hz2_right : z2 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]

    have h_z2_minus_1 : z2 - 1 = starRingEnd ℂ ((-2 : ℂ) + ζ₅^2 + (c : ℂ) * (ζ₅^3 - ζ₅^4)) := by
      simp only [z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_pow, zeta5_conj, map_neg]
      have hpow4_4 : (ζ₅^4)^4 = ζ₅ := by rw [← pow_mul]; norm_num [zeta5_pow_sixteen]
      have hpow4_3 : (ζ₅^4)^3 = ζ₅^2 := by rw [← pow_mul]; norm_num [zeta5_pow_twelve]
      have hpow4_2 : (ζ₅^4)^2 = ζ₅^3 := by rw [← pow_mul]; norm_num [zeta5_pow_eight]
      simp only [hpow4_4, hpow4_3, hpow4_2]
      have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      grind
    rw [h_z2_minus_1, Complex.norm_conj]
    exact cross_disk_z2_bound_restricted c hc_lo hc_hi_le'

  have hz3_right : z3 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC at hz2_right ⊢
    simp only [Set.mem_setOf_eq] at hz2_right ⊢
    simp only [z3]
    rw [show (1 : ℂ) + ζ₅^4 * (z2 - 1) - 1 = ζ₅^4 * (z2 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 4, one_mul]
    exact hz2_right

  have hz3_left : z3 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z3_plus_1 : z3 + 1 = starRingEnd ℂ ((2 : ℂ) - 2*ζ₅ + ζ₅^3 + (c : ℂ) * (ζ₅^4 - 1)) := by
      simp only [z3, z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_pow, zeta5_conj, map_one]
      have hpow4_4 : (ζ₅^4)^4 = ζ₅ := by rw [← pow_mul]; norm_num [zeta5_pow_sixteen]
      have hpow4_3 : (ζ₅^4)^3 = ζ₅^2 := by rw [← pow_mul]; norm_num [zeta5_pow_twelve]
      have hpow4_2 : (ζ₅^4)^2 = ζ₅^3 := by rw [← pow_mul]; norm_num [zeta5_pow_eight]
      simp only [hpow4_4, hpow4_3]
      have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [hconj2]
      ring_nf
      simp only [zeta5_pow_twelve, zeta5_pow_fifteen, zeta5_pow_sixteen]
      ring
    rw [show z3 - (-1 : ℂ) = z3 + 1 by ring, h_z3_plus_1, Complex.norm_conj]
    exact cross_disk_z3_bound_restricted c hc_lo hc_hi_le'

  have hz4_left : z4 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz3_left ⊢
    simp only [Set.mem_setOf_eq] at hz3_left ⊢
    simp only [z4]
    rw [show (-1 : ℂ) + ζ₅^4 * (z3 + 1) - (-1) = ζ₅^4 * (z3 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 4, one_mul]
    grind

  have hz4_right : z4 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z4_minus_1 : z4 - 1 = starRingEnd ℂ ((-2 : ℂ) + 2*ζ₅ - 2*ζ₅^2 + ζ₅^4 + (c : ℂ) * (1 - ζ₅)) := by
      simp only [z4, z3, z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, map_pow, zeta5_conj, map_one, map_neg]
      have hpow4_4 : (ζ₅^4)^4 = ζ₅ := by rw [← pow_mul]; norm_num [zeta5_pow_sixteen]
      have hpow4_3 : (ζ₅^4)^3 = ζ₅^2 := by rw [← pow_mul]; norm_num [zeta5_pow_twelve]
      have hpow4_2 : (ζ₅^4)^2 = ζ₅^3 := by rw [← pow_mul]; norm_num [zeta5_pow_eight]
      simp only [hpow4_4, hpow4_2]
      have hconj2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [hconj2]
      ring_nf
      simp only [zeta5_pow_eight, zeta5_pow_sixteen, zeta5_pow_nineteen, zeta5_pow_twenty]
      ring
    rw [h_z4_minus_1, Complex.norm_conj]
    exact cross_disk_z4_bound_restricted c hc_lo hc_hi_le'

  have h_step1 : applyGen r_crit z0 .A = z1 := by
    exact applyGen_A_formula z0 hz0_left'

  have h_step2 : applyGen r_crit z1 .A = z2 := by
    exact applyGen_A_formula z1 hz1_left

  have h_step3 : applyGen r_crit z2 .B = z3 := by
    exact applyGen_B_formula z2 hz2_right

  have h_step4 : applyGen r_crit z3 .A = z4 := by
    exact applyGen_A_formula z3 hz3_left

  have h_step5 : applyGen r_crit z4 .B = z5 := by
    exact applyGen_B_formula z4 hz4_right

  calc applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .A) .A) .B) .A) .B
      = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z1 .A) .B) .A) .B := by rw [h_step1]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit z2 .B) .A) .B := by rw [h_step2]
    _ = applyGen r_crit (applyGen r_crit z3 .A) .B := by rw [h_step3]
    _ = applyGen r_crit z4 .B := by rw [h_step4]
    _ = z5 := h_step5

end TDCSG.CompoundSymmetry.GG5
