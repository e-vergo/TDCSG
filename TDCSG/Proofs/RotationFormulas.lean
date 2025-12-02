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

lemma exp_neg_two_pi_fifth : Complex.exp ((-2 * π / 5 : ℝ) * I) = ζ₅^4 := by

  have h1 : ((-2 * π / 5 : ℝ) : ℂ) * I = -(2 * ↑π * I / 5) := by push_cast; ring
  rw [h1, Complex.exp_neg]

  have h2 : Complex.exp (2 * ↑π * I / 5) = ζ₅ := by unfold ζ₅ zeta5; rfl
  rw [h2, zeta5_inv_eq_pow4]

lemma genA_rotation_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    genA r_crit z = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold genA
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC leftCenter
  rw [exp_neg_two_pi_fifth]
  ring

lemma genB_rotation_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    genB r_crit z = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold genB
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC rightCenter
  rw [exp_neg_two_pi_fifth]

lemma applyGen_Ainv_formula (z : ℂ)
    (hz : z ∈ leftDisk r_crit)
    (h1 : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit)
    (h2 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) ∈ leftDisk r_crit)
    (h3 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by
  unfold applyGen
  simp only

  rw [genA_rotation_formula z hz]

  rw [genA_rotation_formula _ h1]

  rw [genA_rotation_formula _ h2]

  rw [genA_rotation_formula _ h3]

  have h16 : ζ₅^16 = ζ₅ := zeta5_pow_sixteen
  ring_nf
  simp only [h16]

lemma applyGen_Binv_formula (z : ℂ)
    (hz : z ∈ rightDisk r_crit)
    (h1 : (1 : ℂ) + ζ₅^4 * (z - 1) ∈ rightDisk r_crit)
    (h2 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) ∈ rightDisk r_crit)
    (h3 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) - 1) ∈ rightDisk r_crit) :
    applyGen r_crit z .Binv = (1 : ℂ) + ζ₅ * (z - 1) := by
  unfold applyGen
  simp only
  rw [genB_rotation_formula z hz]
  rw [genB_rotation_formula _ h1]
  rw [genB_rotation_formula _ h2]
  rw [genB_rotation_formula _ h3]
  ring_nf
  simp

lemma applyGen_A_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .A = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold applyGen
  exact genA_rotation_formula z hz

lemma applyGen_B_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .B = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold applyGen
  exact genB_rotation_formula z hz

lemma applyGen_Ainv_formula' (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by

  have h1 : genA r_crit z ∈ leftDisk r_crit := TDCSG.Definitions.genA_preserves_leftDisk r_crit z hz
  have h2 : genA r_crit (genA r_crit z) ∈ leftDisk r_crit :=
    TDCSG.Definitions.genA_preserves_leftDisk r_crit _ h1
  have h3 : genA r_crit (genA r_crit (genA r_crit z)) ∈ leftDisk r_crit :=
    TDCSG.Definitions.genA_preserves_leftDisk r_crit _ h2

  have hf1 : genA r_crit z = (-1 : ℂ) + ζ₅^4 * (z + 1) := genA_rotation_formula z hz
  have hf1' : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit := hf1 ▸ h1
  have hf2_eq : genA r_crit (genA r_crit z) = (-1 : ℂ) + ζ₅^4 * (genA r_crit z + 1) :=
    genA_rotation_formula _ h1
  have hf2' : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) ∈ leftDisk r_crit := by
    have : genA r_crit (genA r_crit z) = (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) := by
      rw [hf2_eq, hf1]
    rw [← this]; exact h2
  have hf3_eq : genA r_crit (genA r_crit (genA r_crit z)) =
      (-1 : ℂ) + ζ₅^4 * (genA r_crit (genA r_crit z) + 1) := genA_rotation_formula _ h2
  have hf3' : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) ∈ leftDisk r_crit := by
    have : genA r_crit (genA r_crit (genA r_crit z)) =
        (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) := by
      rw [hf3_eq, hf2_eq, hf1]
    rw [← this]; exact h3

  exact applyGen_Ainv_formula z hz hf1' hf2' hf3'

lemma applyGen_Binv_formula' (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .Binv = (1 : ℂ) + ζ₅ * (z - 1) := by

  have h1 : genB r_crit z ∈ rightDisk r_crit := TDCSG.Definitions.genB_preserves_rightDisk r_crit z hz
  have h2 : genB r_crit (genB r_crit z) ∈ rightDisk r_crit :=
    TDCSG.Definitions.genB_preserves_rightDisk r_crit _ h1
  have h3 : genB r_crit (genB r_crit (genB r_crit z)) ∈ rightDisk r_crit :=
    TDCSG.Definitions.genB_preserves_rightDisk r_crit _ h2

  have hf1 : genB r_crit z = (1 : ℂ) + ζ₅^4 * (z - 1) := genB_rotation_formula z hz
  have hf1' : (1 : ℂ) + ζ₅^4 * (z - 1) ∈ rightDisk r_crit := hf1 ▸ h1
  have hf2_eq : genB r_crit (genB r_crit z) = (1 : ℂ) + ζ₅^4 * (genB r_crit z - 1) :=
    genB_rotation_formula _ h1
  have hf2' : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) ∈ rightDisk r_crit := by
    have : genB r_crit (genB r_crit z) = (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) := by
      rw [hf2_eq, hf1]
    rw [← this]; exact h2
  have hf3_eq : genB r_crit (genB r_crit (genB r_crit z)) =
      (1 : ℂ) + ζ₅^4 * (genB r_crit (genB r_crit z) - 1) := genB_rotation_formula _ h2
  have hf3' : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) - 1) ∈ rightDisk r_crit := by
    have : genB r_crit (genB r_crit (genB r_crit z)) =
        (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) - 1) := by
      rw [hf3_eq, hf2_eq, hf1]
    rw [← this]; exact h3

  exact applyGen_Binv_formula z hz hf1' hf2' hf3'

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

lemma interval2_c_lower_bound (x : ℝ) (hx : length1 + length2 ≤ x) :
    2 - Real.sqrt 5 ≤ 2 * x - 1 := by
  rw [length12_eq_sqrt5] at hx
  linarith

lemma segmentPoint_eq_smul_E (x : ℝ) : segmentPoint x = (2 * x - 1) • E := by
  unfold segmentPoint E'
  rw [sub_neg_eq_add, show E + E = (2 : ℝ) • E by simp [two_smul], smul_smul]
  rw [show -E + (x * 2) • E = (x * 2 - 1) • E by rw [sub_smul, one_smul]; ring_nf]
  congr 1; ring

lemma segmentPoint_add_displacement (x d : ℝ) :
    segmentPoint (x + d) = segmentPoint x + (2 * d) • E := by
  rw [segmentPoint_eq_smul_E, segmentPoint_eq_smul_E]
  simp only [Complex.real_smul]
  rw [← add_mul]
  congr 1
  push_cast
  ring

end TDCSG.CompoundSymmetry.GG5
