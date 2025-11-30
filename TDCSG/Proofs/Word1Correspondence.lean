/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry

/-!
# Word 1 Correspondence for GG(5,5)

Proves that word1 produces the correct displacement on segment points.

## Main Results

- `word1_produces_displacement0`: word1 maps segment points by displacement0

## TODO

Complete the cross-disk bounds proof for word1 intermediate points.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-- Word 1 action on segment points: translates by displacement0.

word1 = AABAB produces the correct IET translation for interval 0.
Interval 0 corresponds to x ∈ [0, length1), equivalently c ∈ [-1, 2*length1-1].

The proof structure:
1. Segment point x corresponds to complex number (2x-1)•E on segment E'E
2. The word1 generators act as complex rotations (since E'E is in both disks)
3. word1_algebraic_identity shows the 5 rotations produce a translation by 2*displacement0 in the E direction
4. This corresponds to x → x + displacement0 in the segment parameterization

Note: word1 = [Generator.A, Generator.A, Generator.B, Generator.A, Generator.B]
    = [A, A, B, A, B] applied left-to-right -/
lemma word1_produces_displacement0 (x : ℝ) (hx : x ∈ Set.Ico 0 1) (hx_int : x < length1) :
    applyWord r_crit word1 (segmentPoint x) =
    segmentPoint (x + displacement0) := by
  -- Rewrite the RHS using the translation property
  rw [segmentPoint_add_displacement]

  -- Set up parameter c = 2x - 1
  set c := 2 * x - 1 with hc_def
  have hc_lo : -1 ≤ c := by simp only [hc_def]; linarith [hx.1]
  have hc_hi_le : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨hc_lo, hc_hi_le⟩

  -- Express segmentPoint x in terms of c
  have h_z0_eq : segmentPoint x = (c : ℂ) • E := by
    rw [segmentPoint_eq_smul_E, hc_def]
    simp only [Complex.real_smul, smul_eq_mul]

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

  -- Unfold applyWord and word1
  unfold applyWord word1
  simp only [List.foldl_cons, List.foldl_nil]

  -- Define intermediate points (algebraically)
  let z0 := segmentPoint x
  let z1_alg := (-1 : ℂ) + ζ₅^4 * (z0 + 1)           -- After A
  let z2_alg := (-1 : ℂ) + ζ₅^4 * (z1_alg + 1)       -- After A
  let z3_alg := (1 : ℂ) + ζ₅^4 * (z2_alg - 1)        -- After B
  let z4_alg := (-1 : ℂ) + ζ₅^4 * (z3_alg + 1)       -- After A
  let z5_alg := (1 : ℂ) + ζ₅^4 * (z4_alg - 1)        -- After B

  -- The algebraic identity tells us z5_alg = z0 + (2 * displacement0) • E
  have h_alg := word1_algebraic_identity c h_c_mem
  simp only at h_alg

  -- We need to show applyGen computes the same as the algebraic formulas
  -- This requires showing each intermediate point is in the appropriate disk

  -- The key insight: all segment points in [0, length1) have their word1
  -- intermediate points staying within the lens intersection

  -- This proof requires cross-disk bounds for word1.
  -- Placeholder until CrossDiskWord1DiskBounds.lean is completed.
  sorry

end TDCSG.CompoundSymmetry.GG5
