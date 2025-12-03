/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.CrossDiskWord3DiskBounds

/-!
# Word 3 Correspondence

This file proves that applying word3 to points in the third IET interval produces the correct
displacement, establishing the correspondence between the IET and group action for interval 2.

## Main results

- `word3_produces_displacement2`: Word3 produces displacement2 for interval 2 points

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions

/-- For a point `x` in interval 2 (the third IET interval), applying word3 to its image
on the segment E'E produces a translation by `displacement2` along the segment.

This establishes the correspondence between the interval exchange transformation (IET)
and the group action for the third interval of the GG5 system at critical radius.
The word3 sequence `[Ainv, Binv, Ainv, B, A, B]` realizes the IET translation on
points parametrized by `x` in `[length1 + length2, 1)`.

The proof proceeds by:
1. Computing the image of `segmentPoint x` under each generator in word3
2. Verifying at each step that intermediate points remain in the appropriate disks
   (left disk for A/Ainv operations, right disk for B/Binv operations)
3. Using the algebraic identity `word3_algebraic_identity` to confirm the final
   position equals `segmentPoint (x + displacement2)`

This is part of the verification that the IET dynamics on E'E correspond to the
action of words word1, word2, word3 on the three respective intervals, proving
that the origin has infinite orbit under GG5 at critical radius.
See main.tex Theorem "GG5 is infinite at r = sqrt(3 + phi)". -/
lemma word3_produces_displacement2 (x : ℝ) (hx : x ∈ Set.Ico 0 1)
    (hx_interval2 : length1 + length2 ≤ x) :
    applyWord r_crit word3 (segmentPoint x) =
    segmentPoint (x + displacement2) := by

  rw [segmentPoint_add_displacement]

  set c := 2 * x - 1 with hc_def

  have hc_lo : 2 - Real.sqrt 5 ≤ c := interval2_c_lower_bound x hx_interval2
  have hc_hi : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have hc_lo_ge_neg1 : -1 < c := by

    have h_sqrt5_lt_3 : Real.sqrt 5 < 3 := by nlinarith [sqrt5_sq]
    linarith
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hc_lo_ge_neg1, hc_hi⟩

  have h_z0_eq : segmentPoint x = (c : ℂ) • E := by
    rw [segmentPoint_eq_smul_E, hc_def]
    rfl

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

  have h_alg := word3_algebraic_identity c h_c_mem
  simp only at h_alg

  unfold applyWord word3
  simp only [List.foldl_cons, List.foldl_nil]

  rw [h_z0_eq]

  let z0 : ℂ := (c : ℂ) • E
  let z1 := (-1 : ℂ) + ζ₅ * (z0 + 1)
  let z2 := (1 : ℂ) + ζ₅ * (z1 - 1)
  let z3 := (-1 : ℂ) + ζ₅ * (z2 + 1)
  let z4 := (1 : ℂ) + ζ₅^4 * (z3 - 1)
  let z5 := (-1 : ℂ) + ζ₅^4 * (z4 + 1)
  let z6 := (1 : ℂ) + ζ₅^4 * (z5 - 1)

  have h_z6_eq : z6 = z0 + (2 * displacement2) • E := by
    simp only [z6, z5, z4, z3, z2, z1, z0]
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
        (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv) .Ainv) .B)
        .A)
      .B = z6 by
    rw [h, h_z6_eq]

  have hz0_A1_left : (-1 : ℂ) + ζ₅^4 * (z0 + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 z0 hz0_left'
  have hz0_A2_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 _ hz0_A1_left
  have hz0_A3_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 _ hz0_A2_left

  have hz1_left : z1 ∈ leftDisk r_crit := by
    simp only [z1]
    have h := leftDisk_zeta_rotation r_crit 1 z0 hz0_left'
    simpa using h

  have hz1_right : z1 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq, z1]
    have h_z1_minus_1 : (-1 : ℂ) + ζ₅ * (z0 + 1) - 1 = starRingEnd ℂ ((ζ₅^4 - 2) + (c : ℂ) * (1 - ζ₅)) := by
      simp only [z0, E]
      rw [smul_eq_mul]
      have h_expand_lhs : (-1 : ℂ) + ζ₅ * ((c : ℂ) * (ζ₅^4 - ζ₅^3) + 1) - 1 =
          c - c * ζ₅^4 + ζ₅ - 2 := by
        calc (-1 : ℂ) + ζ₅ * ((c : ℂ) * (ζ₅^4 - ζ₅^3) + 1) - 1
            = -1 + c * ζ₅ * (ζ₅^4 - ζ₅^3) + ζ₅ - 1 := by ring
          _ = -1 + c * (ζ₅^5 - ζ₅^4) + ζ₅ - 1 := by ring
          _ = -1 + c * (1 - ζ₅^4) + ζ₅ - 1 := by simp only [zeta5_pow_five]
          _ = c - c * ζ₅^4 + ζ₅ - 2 := by ring
      have h_expand_rhs : starRingEnd ℂ ((ζ₅^4 - 2) + (c : ℂ) * (1 - ζ₅)) =
          ζ₅ - 2 + c - c * ζ₅^4 := by
        simp only [map_add, map_sub, map_mul, map_one, Complex.conj_ofReal]
        rw [zeta5_conj, show starRingEnd ℂ (ζ₅^4) = ζ₅ by
          rw [map_pow, zeta5_conj]
          calc (ζ₅^4)^4 = ζ₅^16 := by ring
            _ = ζ₅^(16 % 5) := by rw [zeta5_pow_reduce 16]
            _ = ζ₅^1 := by norm_num
            _ = ζ₅ := pow_one ζ₅]
        have h2 : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_ofReal 2
        rw [h2]
        ring
      rw [h_expand_lhs, h_expand_rhs]
      ring
    rw [h_z1_minus_1, Complex.norm_conj]
    exact cross_disk_w3_z1_bound c hc_lo hc_hi

  have hz1_B1_right : (1 : ℂ) + ζ₅^4 * (z1 - 1) ∈ rightDisk r_crit :=
    rightDisk_zeta_rotation r_crit 4 z1 hz1_right

  have hz1_B2_right : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) ∈ rightDisk r_crit :=
    rightDisk_zeta_rotation r_crit 4 _ hz1_B1_right

  have hz1_B3_right : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) - 1) ∈ rightDisk r_crit :=
    rightDisk_zeta_rotation r_crit 4 _ hz1_B2_right

  have hz2_right : z2 ∈ rightDisk r_crit := by
    simp only [z2]
    have h := rightDisk_zeta_rotation r_crit 1 z1 hz1_right
    simpa using h

  have hz2_left : z2 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z2_plus_1 : z2 + 1 = starRingEnd ℂ (((2 : ℂ) + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)) := by
      simp only [z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, map_one, Complex.conj_ofReal,
                 map_pow, zeta5_conj]
      have hpow4_3 : (ζ₅^4)^3 = ζ₅^2 := by
        calc (ζ₅^4)^3 = ζ₅^12 := by ring
          _ = ζ₅^2 := zeta5_pow_twelve
      have hpow4_4 : (ζ₅^4)^4 = ζ₅ := by
        calc (ζ₅^4)^4 = ζ₅^16 := by ring
          _ = ζ₅ := zeta5_pow_sixteen
      simp only [hpow4_3, hpow4_4]
      have hconj2_nat : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [hconj2_nat]
      ring_nf
      simp only [zeta5_pow_five, zeta5_pow_six]
      ring
    rw [show z2 - (-1 : ℂ) = z2 + 1 by ring, h_z2_plus_1, Complex.norm_conj]
    exact cross_disk_w3_z2_bound c hc_lo hc_hi

  have hz2_A1_left : (-1 : ℂ) + ζ₅^4 * (z2 + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 z2 hz2_left

  have hz2_A2_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 _ hz2_A1_left

  have hz2_A3_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 _ hz2_A2_left

  have hz3_left : z3 ∈ leftDisk r_crit := by
    simp only [z3]
    have h := leftDisk_zeta_rotation r_crit 1 z2 hz2_left
    simpa using h

  have hz3_right : z3 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z3_minus_1 : z3 - 1 = starRingEnd ℂ (((-2 : ℂ) + ζ₅^2 - 2*ζ₅^3 + 2*ζ₅^4) + (c : ℂ) * (ζ₅^3 - ζ₅^4)) := by
      simp only [z3, z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, map_neg, Complex.conj_ofReal, map_pow, zeta5_conj]
      have hpow4_2 : (ζ₅^4)^2 = ζ₅^3 := by simp only [← pow_mul]; exact zeta5_pow_eight
      have hpow4_3 : (ζ₅^4)^3 = ζ₅^2 := by simp only [← pow_mul]; exact zeta5_pow_twelve
      have hconj2_nat : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [hpow4_2, hpow4_3, hconj2_nat]
      ring_nf
      simp only [zeta5_pow_six, zeta5_pow_seven, zeta5_pow_sixteen]
      grind only
    rw [h_z3_minus_1, Complex.norm_conj]
    exact cross_disk_w3_z3_bound c hc_lo hc_hi

  have hz4_left : z4 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z4_plus_1 : z4 + 1 = starRingEnd ℂ (((4 : ℂ) - 2*ζ₅ + ζ₅^3 - 2*ζ₅^4) + (c : ℂ) * (ζ₅^4 - 1)) := by
      simp only [z4, z3, z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, map_one, Complex.conj_ofReal, map_pow, zeta5_conj]
      have hpow4_2 : (ζ₅^4)^2 = ζ₅^3 := by simp only [← pow_mul]; exact zeta5_pow_eight
      have hpow4_3 : (ζ₅^4)^3 = ζ₅^2 := by simp only [← pow_mul]; exact zeta5_pow_twelve
      have hpow4_4 : (ζ₅^4)^4 = ζ₅ := by simp only [← pow_mul]; exact zeta5_pow_sixteen
      have hconj4_nat : (starRingEnd ℂ) (4 : ℂ) = 4 := Complex.conj_ofReal 4
      have hconj2_nat : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [hpow4_3, hpow4_4, hconj4_nat, hconj2_nat]
      ring_nf
      simp only [zeta5_pow_five, one_mul, zeta5_pow_six, zeta5_pow_seven, zeta5_pow_ten,
        zeta5_pow_eleven]
      grind only

    rw [show z4 - (-1 : ℂ) = z4 + 1 by ring, h_z4_plus_1, Complex.norm_conj]
    exact cross_disk_w3_z4_bound c hc_lo hc_hi

  have hz4_right : z4 ∈ rightDisk r_crit := by
    simp only [z4]
    have h := rightDisk_zeta_rotation r_crit 4 z3 hz3_right
    simpa using h

  have hz5_left : z5 ∈ leftDisk r_crit := by
    simp only [z5]
    exact leftDisk_zeta_rotation r_crit 4 z4 hz4_left

  have hz5_right : z5 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    have h_z5_minus_1 : z5 - 1 = starRingEnd ℂ (((-4 : ℂ) + 4*ζ₅ - 2*ζ₅^2 + ζ₅^4) + (c : ℂ) * (1 - ζ₅)) := by
      simp only [z5, z4, z3, z2, z1, z0, E]
      rw [smul_eq_mul]
      simp only [map_add, map_sub, map_mul, map_neg, map_one, Complex.conj_ofReal,
                 map_pow, zeta5_conj]
      have hpow4_4 : (ζ₅^4)^4 = ζ₅ := by simp only [← pow_mul]; exact zeta5_pow_sixteen
      have hpow4_2 : (ζ₅^4)^2 = ζ₅^3 := by simp only [← pow_mul]; exact zeta5_pow_eight
      have hconj4_nat : (starRingEnd ℂ) (4 : ℂ) = 4 := Complex.conj_ofReal 4
      have hconj2_nat : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
      simp only [hpow4_4, hpow4_2, hconj4_nat, hconj2_nat]
      ring_nf
      simp only [zeta5_pow_eight, zeta5_pow_nine, zeta5_pow_ten, one_mul, zeta5_pow_eleven,
        zeta5_pow_fourteen, zeta5_pow_fifteen, add_left_inj]
      grind only
    rw [h_z5_minus_1, Complex.norm_conj]
    exact cross_disk_w3_z5_bound c hc_lo hc_hi

  have h_step1 : applyGen r_crit z0 .Ainv = z1 := by
    exact applyGen_Ainv_formula z0 hz0_left' hz0_A1_left hz0_A2_left hz0_A3_left

  have h_step2 : applyGen r_crit z1 .Binv = z2 := by
    exact applyGen_Binv_formula z1 hz1_right hz1_B1_right hz1_B2_right hz1_B3_right

  have h_step3 : applyGen r_crit z2 .Ainv = z3 := by
    exact applyGen_Ainv_formula z2 hz2_left hz2_A1_left hz2_A2_left hz2_A3_left

  have h_step4 : applyGen r_crit z3 .B = z4 := by
    exact applyGen_B_formula z3 hz3_right

  have h_step5 : applyGen r_crit z4 .A = z5 := by
    exact applyGen_A_formula z4 hz4_left

  have h_step6 : applyGen r_crit z5 .B = z6 := by
    exact applyGen_B_formula z5 hz5_right

  calc applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv) .Ainv) .B) .A) .B
      = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z1 .Binv) .Ainv) .B) .A) .B := by rw [h_step1]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z2 .Ainv) .B) .A) .B := by rw [h_step2]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit z3 .B) .A) .B := by rw [h_step3]
    _ = applyGen r_crit (applyGen r_crit z4 .A) .B := by rw [h_step4]
    _ = applyGen r_crit z5 .B := by rw [h_step5]
    _ = z6 := h_step6

end TDCSG.CompoundSymmetry.GG5
