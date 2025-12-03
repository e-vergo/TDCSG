/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points
import TDCSG.Proofs.Zeta5
import TDCSG.Proofs.IET

/-!
# Rotation Formulas for Group Generators

This file derives explicit formulas for the generators A and B and their inverses in terms of
roots of unity, and establishes the relationship between segment points and the vector E.

## Main results

- `genA_rotation_formula`: Generator A rotates by ζ₅⁴ about the left disk center
- `genB_rotation_formula`: Generator B rotates by ζ₅⁴ about the right disk center
- `applyGen_Ainv_formula'`: A⁻¹ rotates by ζ₅ about the left disk center
- `applyGen_Binv_formula'`: B⁻¹ rotates by ζ₅ about the right disk center
- `segmentPoint_eq_smul_E`: Segment points are multiples of E

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

open Complex Real
open TDCSG.Definitions

namespace TDCSG.CompoundSymmetry.GG5

/-- The complex exponential of -2π/5 radians equals ζ₅⁴.

This converts between the real-valued angle representation and the algebraic
fifth root of unity representation. Since ζ₅ = exp(2πi/5), we have
exp(-2πi/5) = ζ₅⁻¹ = ζ₅⁴ by the primitive root property. -/
lemma exp_neg_two_pi_fifth : Complex.exp ((-2 * π / 5 : ℝ) * I) = ζ₅^4 := by

  have h1 : ((-2 * π / 5 : ℝ) : ℂ) * I = -(2 * ↑π * I / 5) := by push_cast; ring
  rw [h1, Complex.exp_neg]

  have h2 : Complex.exp (2 * ↑π * I / 5) = ζ₅ := by unfold ζ₅; rfl
  rw [h2, zeta5_inv_eq_pow4]

/-- Generator A rotates points by ζ₅⁴ about the left disk center (-1).

For GG₅, the generator A performs clockwise rotation by 2π/5 (equivalently,
multiplication by ζ₅⁴) about the center of the left disk. This formula
expresses genA in terms of roots of unity rather than complex exponentials. -/
lemma genA_rotation_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    genA r_crit z = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold genA
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC leftCenter
  rw [exp_neg_two_pi_fifth]
  ring

/-- Generator B rotates points by ζ₅⁴ about the right disk center (+1).

For GG₅, the generator B performs clockwise rotation by 2π/5 (equivalently,
multiplication by ζ₅⁴) about the center of the right disk. This is the
symmetric counterpart to `genA_rotation_formula`. -/
lemma genB_rotation_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    genB r_crit z = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold genB
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC rightCenter
  rw [exp_neg_two_pi_fifth]

/-- Rotation by ζ₅^k about -1 preserves leftDisk membership. -/
lemma leftDisk_zeta_rotation (r : ℝ) (k : ℕ) (z : ℂ) (hz : z ∈ leftDisk r) :
    (-1 : ℂ) + ζ₅^k * (z + 1) ∈ leftDisk r := by
  unfold leftDisk closedDiskC at hz ⊢
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [show (-1 : ℂ) + ζ₅^k * (z + 1) - (-1) = ζ₅^k * (z + 1) by ring]
  rw [Complex.norm_mul, zeta5_abs_pow k, one_mul]
  convert hz using 2
  ring

/-- Rotation by ζ₅^k about +1 preserves rightDisk membership. -/
lemma rightDisk_zeta_rotation (r : ℝ) (k : ℕ) (z : ℂ) (hz : z ∈ rightDisk r) :
    (1 : ℂ) + ζ₅^k * (z - 1) ∈ rightDisk r := by
  unfold rightDisk closedDiskC at hz ⊢
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [show (1 : ℂ) + ζ₅^k * (z - 1) - 1 = ζ₅^k * (z - 1) by ring]
  rw [Complex.norm_mul, zeta5_abs_pow k, one_mul]
  exact hz

/-- A⁻¹ rotates by ζ₅ about the left disk center, given explicit membership hypotheses.

Since A⁻¹ = A⁴ in the cyclic group of order 5, applying A four times is equivalent
to counterclockwise rotation by 2π/5, i.e., multiplication by ζ₅. This version
requires explicit proof that intermediate points remain in the left disk. -/
lemma applyGen_Ainv_formula (z : ℂ)
    (hz : z ∈ leftDisk r_crit)
    (h1 : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit)
    (h2 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) ∈ leftDisk r_crit)
    (h3 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by
  unfold applyGen
  simp only [Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply]

  rw [genA_rotation_formula z hz]

  rw [genA_rotation_formula _ h1]

  rw [genA_rotation_formula _ h2]

  rw [genA_rotation_formula _ h3]

  have h16 : ζ₅^16 = ζ₅ := zeta5_pow_sixteen
  ring_nf
  simp only [h16]

/-- B⁻¹ rotates by ζ₅ about the right disk center, given explicit membership hypotheses.

Since B⁻¹ = B⁴ in the cyclic group of order 5, applying B four times is equivalent
to counterclockwise rotation by 2π/5, i.e., multiplication by ζ₅. This version
requires explicit proof that intermediate points remain in the right disk. -/
lemma applyGen_Binv_formula (z : ℂ)
    (hz : z ∈ rightDisk r_crit)
    (h1 : (1 : ℂ) + ζ₅^4 * (z - 1) ∈ rightDisk r_crit)
    (h2 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) ∈ rightDisk r_crit)
    (h3 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) - 1) ∈ rightDisk r_crit) :
    applyGen r_crit z .Binv = (1 : ℂ) + ζ₅ * (z - 1) := by
  unfold applyGen
  simp only [Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply]
  rw [genB_rotation_formula z hz]
  rw [genB_rotation_formula _ h1]
  rw [genB_rotation_formula _ h2]
  rw [genB_rotation_formula _ h3]
  ring_nf
  simp

/-- Generator A expressed via `applyGen`: rotation by ζ₅⁴ about the left center. -/
lemma applyGen_A_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .A = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold applyGen
  exact genA_rotation_formula z hz

/-- Generator B expressed via `applyGen`: rotation by ζ₅⁴ about the right center. -/
lemma applyGen_B_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .B = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold applyGen
  exact genB_rotation_formula z hz

/-- A⁻¹ rotates by ζ₅ about the left disk center (-1).

This is the user-friendly version that automatically derives disk membership
for intermediate points using `leftDisk_zeta_rotation`. Counterclockwise
rotation by 2π/5 is multiplication by ζ₅ = exp(2πi/5). -/
lemma applyGen_Ainv_formula' (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by
  have h1 : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit := leftDisk_zeta_rotation r_crit 4 z hz
  have h2 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 _ h1
  have h3 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) ∈ leftDisk r_crit :=
    leftDisk_zeta_rotation r_crit 4 _ h2
  exact applyGen_Ainv_formula z hz h1 h2 h3

/-- B⁻¹ rotates by ζ₅ about the right disk center (+1).

This is the user-friendly version that automatically derives disk membership
for intermediate points using `rightDisk_zeta_rotation`. Counterclockwise
rotation by 2π/5 is multiplication by ζ₅ = exp(2πi/5). -/
lemma applyGen_Binv_formula' (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .Binv = (1 : ℂ) + ζ₅ * (z - 1) := by
  have h1 : (1 : ℂ) + ζ₅^4 * (z - 1) ∈ rightDisk r_crit := rightDisk_zeta_rotation r_crit 4 z hz
  have h2 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) ∈ rightDisk r_crit :=
    rightDisk_zeta_rotation r_crit 4 _ h1
  have h3 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) - 1) ∈ rightDisk r_crit :=
    rightDisk_zeta_rotation r_crit 4 _ h2
  exact applyGen_Binv_formula z hz h1 h2 h3

/-- The sum of interval lengths length1 + length2 equals (3 - sqrt(5))/2.

This establishes the relationship between the IET interval lengths defined in
terms of the golden ratio and their explicit algebraic form. Since
1/(1 + phi) = (3 - sqrt(5))/2, this provides a more computable representation. -/
lemma length12_eq_sqrt5 : length1 + length2 = (3 - Real.sqrt 5) / 2 := by
  have h_goldenRatio : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := Real.goldenRatio.eq_1
  have h_one_plus_phi : (1 : ℝ) + Real.goldenRatio = (3 + Real.sqrt 5) / 2 := by
    rw [h_goldenRatio]; ring
  rw [length12_sum, h_one_plus_phi]
  have h_denom_ne : (3 + Real.sqrt 5) ≠ 0 := by
    have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
    linarith
  field_simp

  nlinarith [sqrt5_sq]

/-- Lower bound on 2x - 1 when x is in the third IET interval.

For x >= length1 + length2, the transformed coordinate 2x - 1 satisfies
2 - sqrt(5) <= 2x - 1. This bound is used when analyzing segment point
positions in the third interval of the interval exchange transformation. -/
lemma interval2_c_lower_bound (x : ℝ) (hx : length1 + length2 ≤ x) :
    2 - Real.sqrt 5 ≤ 2 * x - 1 := by
  rw [length12_eq_sqrt5] at hx
  linarith

/-- Segment points are scalar multiples of E.

The segment E'E (from -E to E) is parameterized by segmentPoint(x) for x in [0,1].
This lemma shows segmentPoint(x) = (2x - 1) * E, making the linear structure
explicit: at x=0 we get -E, at x=1/2 we get 0, and at x=1 we get E. -/
lemma segmentPoint_eq_smul_E (x : ℝ) : segmentPoint x = (2 * x - 1) • E := by
  unfold segmentPoint E'
  rw [sub_neg_eq_add, show E + E = (2 : ℝ) • E by simp [two_smul], smul_smul]
  rw [show -E + (x * 2) • E = (x * 2 - 1) • E by rw [sub_smul, one_smul]; ring_nf]
  congr 1; ring

/-- Displacement along the segment E'E is linear in E.

Adding d to the parameter x shifts the segment point by 2d * E. This captures
the fact that the segment has length 2|E| and segmentPoint is a linear
parameterization. Used to analyze translations induced by the IET. -/
lemma segmentPoint_add_displacement (x d : ℝ) :
    segmentPoint (x + d) = segmentPoint x + (2 * d) • E := by
  rw [segmentPoint_eq_smul_E, segmentPoint_eq_smul_E]
  simp only [Complex.real_smul]
  rw [← add_mul]
  congr 1
  push_cast
  ring

end TDCSG.CompoundSymmetry.GG5
