/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.CrossDiskWord3DiskBounds

/-!
# Word 3 Correspondence for GG(5,5)

Proves that word3 produces the correct displacement on segment points.

## Main Results

- `word3_produces_displacement2`: word3 maps segment points by displacement2

This is the completed proof using the cross-disk bounds from CrossDiskWord3DiskBounds.lean.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions hiding φ r_crit

/-- Word 3 action on segment points: translates by displacement2.

word3 = A⁻¹B⁻¹A⁻¹BAB produces the correct IET translation for interval 2.

The proof structure:
1. Segment point x corresponds to complex number (2x-1)•E on segment E'E
2. The word3 generators act as complex rotations (since E'E is in both disks)
3. The algebraic identity word3_algebraic_identity shows the 6 rotations
   produce a translation by 2*displacement2 in the E direction
4. This corresponds to x → x + displacement2 in the segment parameterization

Note: word3 = [Generator.Ainv, Generator.Binv, Generator.Ainv, Generator.B, Generator.A, Generator.B]
    = [A⁻¹, B⁻¹, A⁻¹, B, A, B] applied left-to-right -/
lemma word3_produces_displacement2 (x : ℝ) (hx : x ∈ Set.Ico 0 1)
    (hx_interval2 : length1 + length2 ≤ x) :
    applyWord r_crit word3 (segmentPoint x) =
    segmentPoint (x + displacement2) := by
  -- Rewrite the RHS using the translation property
  rw [segmentPoint_add_displacement]

  -- Set up parameter c = 2x - 1
  set c := 2 * x - 1 with hc_def

  -- Derive bounds on c from interval 2 constraints
  have hc_lo : 2 - Real.sqrt 5 ≤ c := interval2_c_lower_bound x hx_interval2
  have hc_hi : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have hc_lo_ge_neg1 : -1 < c := by
    -- 2 - √5 > -1 since √5 < 3
    have h_sqrt5_lt_3 : Real.sqrt 5 < 3 := by nlinarith [sqrt5_sq]
    linarith
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hc_lo_ge_neg1, hc_hi⟩

  -- Express segmentPoint x in terms of c
  have h_z0_eq : segmentPoint x = (c : ℂ) • E := by
    rw [segmentPoint_eq_smul_E, hc_def]
    rfl

  -- Get disk membership for the starting point
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

  -- The algebraic identity tells us what the 6-step rotation produces
  have h_alg := word3_algebraic_identity c h_c_mem
  simp only at h_alg

  -- Unfold applyWord and word3
  unfold applyWord word3
  simp only [List.foldl_cons, List.foldl_nil]

  -- Rewrite using h_z0_eq to convert segmentPoint x to c • E
  rw [h_z0_eq]

  -- Define the intermediate algebraic points (from word3_algebraic_identity)
  let z0 : ℂ := (c : ℂ) • E
  let z1 := (-1 : ℂ) + ζ₅ * (z0 + 1)
  let z2 := (1 : ℂ) + ζ₅ * (z1 - 1)
  let z3 := (-1 : ℂ) + ζ₅ * (z2 + 1)
  let z4 := (1 : ℂ) + ζ₅^4 * (z3 - 1)
  let z5 := (-1 : ℂ) + ζ₅^4 * (z4 + 1)
  let z6 := (1 : ℂ) + ζ₅^4 * (z5 - 1)

  -- The algebraic identity tells us z6 = z0 + (2 * displacement2) • E
  have h_z6_eq : z6 = z0 + (2 * displacement2) • E := by
    simp only [z6, z5, z4, z3, z2, z1, z0]
    convert h_alg using 1

  -- Disk membership for z0 (already proven above via hz0_left, hz0_right)
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

  -- Disk membership for intermediate points in A⁻¹ chain on z0.
  have hz0_A1_left : (-1 : ℂ) + ζ₅^4 * (z0 + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_left' ⊢
    simp only [Set.mem_setOf_eq] at hz0_left' ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * (z0 + 1) - (-1) = ζ₅^4 * (z0 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    simp only [one_mul]
    convert hz0_left' using 2
    ring
  have hz0_A2_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_A1_left ⊢
    simp only [Set.mem_setOf_eq] at hz0_A1_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) - (-1) =
        ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    simp only [one_mul]
    convert hz0_A1_left using 2
    ring
  have hz0_A3_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_A2_left ⊢
    simp only [Set.mem_setOf_eq] at hz0_A2_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) - (-1) =
        ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    simp only [one_mul]
    convert hz0_A2_left using 2
    ring

  -- z1 = applyGen z0 .Ainv is in both disks
  have hz1_left : z1 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_left' ⊢
    simp only [Set.mem_setOf_eq] at hz0_left' ⊢
    simp only [z1]
    rw [show (-1 : ℂ) + ζ₅ * (z0 + 1) - (-1) = ζ₅ * (z0 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    convert hz0_left' using 2
    ring

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

  -- Disk membership for intermediate points in B⁻¹ chain on z1
  have hz1_B1_right : (1 : ℂ) + ζ₅^4 * (z1 - 1) ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC at hz1_right ⊢
    simp only [Set.mem_setOf_eq] at hz1_right ⊢
    rw [show (1 : ℂ) + ζ₅^4 * (z1 - 1) - 1 = ζ₅^4 * (z1 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 4, one_mul]
    exact hz1_right

  have hz1_B2_right : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC at hz1_right ⊢
    simp only [Set.mem_setOf_eq] at hz1_right ⊢
    rw [show (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) - 1 = ζ₅^8 * (z1 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 8, one_mul]
    exact hz1_right

  have hz1_B3_right : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) - 1) ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC at hz1_right ⊢
    simp only [Set.mem_setOf_eq] at hz1_right ⊢
    rw [show (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) - 1) - 1 = ζ₅^12 * (z1 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 12, one_mul]
    exact hz1_right

  -- z2 is in rightDisk by rotation (z2 - 1 = ζ₅*(z1 - 1))
  have hz2_right : z2 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC at hz1_right ⊢
    simp only [Set.mem_setOf_eq] at hz1_right ⊢
    simp only [z2]
    rw [show (1 : ℂ) + ζ₅ * (z1 - 1) - 1 = ζ₅ * (z1 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    exact hz1_right

  -- z2 in leftDisk requires cross_disk_w3_z2_bound
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

  -- Disk membership for intermediate points in A⁻¹ chain on z2
  have hz2_A1_left : (-1 : ℂ) + ζ₅^4 * (z2 + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz2_left ⊢
    simp only [Set.mem_setOf_eq] at hz2_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * (z2 + 1) - (-1) = ζ₅^4 * (z2 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 4, one_mul]
    convert hz2_left using 2; ring

  have hz2_A2_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz2_left ⊢
    simp only [Set.mem_setOf_eq] at hz2_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) - (-1) = ζ₅^8 * (z2 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 8, one_mul]
    convert hz2_left using 2; ring

  have hz2_A3_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz2_left ⊢
    simp only [Set.mem_setOf_eq] at hz2_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) + 1) - (-1) = ζ₅^12 * (z2 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 12, one_mul]
    convert hz2_left using 2; ring

  -- z3 is in leftDisk by rotation
  have hz3_left : z3 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz2_left ⊢
    simp only [Set.mem_setOf_eq] at hz2_left ⊢
    simp only [z3]
    rw [show (-1 : ℂ) + ζ₅ * (z2 + 1) - (-1) = ζ₅ * (z2 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    convert hz2_left using 2; ring

  -- z3 in rightDisk requires cross_disk_w3_z3_bound
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

  -- z4 in leftDisk requires cross_disk_w3_z4_bound
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

  -- z4 is in rightDisk by rotation
  have hz4_right : z4 ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC at hz3_right ⊢
    simp only [Set.mem_setOf_eq] at hz3_right ⊢
    simp only [z4]
    rw [show (1 : ℂ) + ζ₅^4 * (z3 - 1) - 1 = ζ₅^4 * (z3 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 4, one_mul]
    exact hz3_right

  -- z5 is in leftDisk by rotation
  have hz5_left : z5 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz4_left ⊢
    simp only [Set.mem_setOf_eq] at hz4_left ⊢
    simp only [z5]
    rw [show (-1 : ℂ) + ζ₅^4 * (z4 + 1) - (-1) = ζ₅^4 * (z4 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow 4, one_mul]
    convert hz4_left using 2; ring

  -- z5 in rightDisk requires cross_disk_w3_z5_bound
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

  -- Now chain through the 6 steps
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

  -- Chain all steps together
  calc applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv) .Ainv) .B) .A) .B
      = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z1 .Binv) .Ainv) .B) .A) .B := by rw [h_step1]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z2 .Ainv) .B) .A) .B := by rw [h_step2]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit z3 .B) .A) .B := by rw [h_step3]
    _ = applyGen r_crit (applyGen r_crit z4 .A) .B := by rw [h_step4]
    _ = applyGen r_crit z5 .B := by rw [h_step5]
    _ = z6 := h_step6

end TDCSG.CompoundSymmetry.GG5
