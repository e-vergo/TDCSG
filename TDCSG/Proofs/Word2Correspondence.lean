import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.CrossDiskWord2DiskBounds

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions

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
    unfold leftDisk closedDiskC at hz0_left' ⊢
    simp only [Set.mem_setOf_eq] at hz0_left' ⊢
    simp only [z1]
    rw [show (-1 : ℂ) + ζ₅ * (z0 + 1) - (-1) = ζ₅ * (z0 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    convert hz0_left' using 2
    ring

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
    unfold rightDisk closedDiskC at hz1_right ⊢
    simp only [Set.mem_setOf_eq] at hz1_right ⊢
    simp only [z2]
    rw [show (1 : ℂ) + ζ₅ * (z1 - 1) - 1 = ζ₅ * (z1 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    exact hz1_right

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
    unfold leftDisk closedDiskC at hz2_left ⊢
    simp only [Set.mem_setOf_eq] at hz2_left ⊢
    simp only [z3]
    rw [show (-1 : ℂ) + ζ₅ * (z2 + 1) - (-1) = ζ₅ * (z2 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    convert hz2_left using 2; ring

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
    unfold rightDisk closedDiskC at hz3_right ⊢
    simp only [Set.mem_setOf_eq] at hz3_right ⊢
    simp only [z4]
    rw [show (1 : ℂ) + ζ₅ * (z3 - 1) - 1 = ζ₅ * (z3 - 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    exact hz3_right

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
