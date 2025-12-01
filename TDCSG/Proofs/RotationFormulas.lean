/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points
import TDCSG.Proofs.Zeta5
import TDCSG.Proofs.IET

/-!
# Rotation Formulas for GG(5,5)

Lemmas relating rotation angles to the 5th root of unity ζ₅ and
formulas for applying generators A, B, A⁻¹, B⁻¹.
-/

open Complex Real TDCSG.Definitions

namespace TDCSG.CompoundSymmetry.GG5

/-- Helper: exp(-2πi/5) = ζ₅⁴.
    This connects the rotation angle used in genA/genB to the 5th root of unity. -/
lemma exp_neg_two_pi_fifth : Complex.exp ((-2 * π / 5 : ℝ) * I) = ζ₅^4 := by
  -- exp(-2πi/5) = exp(2πi/5)^(-1) = ζ₅^(-1) = ζ₅^4
  have h1 : ((-2 * π / 5 : ℝ) : ℂ) * I = -(2 * ↑π * I / 5) := by push_cast; ring
  rw [h1, Complex.exp_neg]
  -- Now: ⊢ (cexp (2 * ↑π * I / 5))⁻¹ = ζ₅ ^ 4
  have h2 : Complex.exp (2 * ↑π * I / 5) = ζ₅ := by unfold ζ₅ zeta5; rfl
  rw [h2, zeta5_inv_eq_pow4]

/-- Helper: genA on a point in leftDisk computes the rotation formula. -/
lemma genA_rotation_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    genA r_crit z = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold genA
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC leftCenter
  rw [exp_neg_two_pi_fifth]
  ring

/-- Helper: genB on a point in rightDisk computes the rotation formula. -/
lemma genB_rotation_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    genB r_crit z = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold genB
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC rightCenter
  rw [exp_neg_two_pi_fifth]

/-- Helper: exp(2πi/5) = ζ₅.
    This connects the positive rotation angle to the primitive 5th root of unity. -/
lemma exp_two_pi_fifth : Complex.exp ((2 * π / 5 : ℝ) * I) = ζ₅ := by
  unfold ζ₅ zeta5
  congr 1
  push_cast
  ring

/-- Helper: When all intermediate points in A⁴ chain are in leftDisk,
    applyGen .Ainv computes the inverse rotation formula: -1 + ζ₅ * (z + 1).

    This follows from: A uses ζ₅^4 rotation, so A⁴ uses (ζ₅^4)^4 = ζ₅^16 = ζ₅. -/
lemma applyGen_Ainv_formula (z : ℂ)
    (hz : z ∈ leftDisk r_crit)
    (h1 : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit)
    (h2 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) ∈ leftDisk r_crit)
    (h3 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by
  unfold applyGen
  simp only
  -- First application
  rw [genA_rotation_formula z hz]
  -- Second application
  rw [genA_rotation_formula _ h1]
  -- Third application
  rw [genA_rotation_formula _ h2]
  -- Fourth application
  rw [genA_rotation_formula _ h3]
  -- Now simplify: (ζ₅^4)^4 = ζ₅^16 = ζ₅
  have h16 : ζ₅^16 = ζ₅ := zeta5_pow_sixteen
  ring_nf
  simp only [h16]

/-- Helper: When all intermediate points in B⁴ chain are in rightDisk,
    applyGen .Binv computes the inverse rotation formula: 1 + ζ₅ * (z - 1). -/
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

/-- Helper: applyGen .A computes the forward rotation formula. -/
lemma applyGen_A_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .A = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold applyGen
  exact genA_rotation_formula z hz

/-- Helper: applyGen .B computes the forward rotation formula. -/
lemma applyGen_B_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .B = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold applyGen
  exact genB_rotation_formula z hz

/-- Simplified Ainv formula: Only requires initial disk membership.
    Uses genA_preserves_leftDisk to derive chain membership automatically. -/
lemma applyGen_Ainv_formula' (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by
  -- Derive chain membership using preservation lemma
  have h1 : genA r_crit z ∈ leftDisk r_crit := TDCSG.Definitions.genA_preserves_leftDisk r_crit z hz
  have h2 : genA r_crit (genA r_crit z) ∈ leftDisk r_crit :=
    TDCSG.Definitions.genA_preserves_leftDisk r_crit _ h1
  have h3 : genA r_crit (genA r_crit (genA r_crit z)) ∈ leftDisk r_crit :=
    TDCSG.Definitions.genA_preserves_leftDisk r_crit _ h2
  -- Translate chain membership to explicit form
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
  -- Apply the original Ainv formula
  exact applyGen_Ainv_formula z hz hf1' hf2' hf3'

/-- Simplified Binv formula: Only requires initial disk membership.
    Uses genB_preserves_rightDisk to derive chain membership automatically. -/
lemma applyGen_Binv_formula' (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .Binv = (1 : ℂ) + ζ₅ * (z - 1) := by
  -- Derive chain membership using preservation lemma
  have h1 : genB r_crit z ∈ rightDisk r_crit := TDCSG.Definitions.genB_preserves_rightDisk r_crit z hz
  have h2 : genB r_crit (genB r_crit z) ∈ rightDisk r_crit :=
    TDCSG.Definitions.genB_preserves_rightDisk r_crit _ h1
  have h3 : genB r_crit (genB r_crit (genB r_crit z)) ∈ rightDisk r_crit :=
    TDCSG.Definitions.genB_preserves_rightDisk r_crit _ h2
  -- Translate chain membership to explicit form
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
  -- Apply the original Binv formula
  exact applyGen_Binv_formula z hz hf1' hf2' hf3'

/-- Convenience: length1 + length2 = (3 - √5)/2. -/
lemma length12_eq_sqrt5 : length1 + length2 = (3 - Real.sqrt 5) / 2 := by
  have h_goldenRatio : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := Real.goldenRatio.eq_1
  have h_one_plus_phi : (1 : ℝ) + Real.goldenRatio = (3 + Real.sqrt 5) / 2 := by
    rw [h_goldenRatio]; ring
  rw [length12_sum, h_one_plus_phi]
  have h_denom_ne : (3 + Real.sqrt 5) ≠ 0 := by
    have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
    linarith
  field_simp
  -- (3 - √5) * 2 = 2 * (3 + √5) / (3 + √5) * (3 - √5)
  -- Need: 2 * (3 - √5) = 2 * (9 - 5) / (3 + √5) ... no
  -- Actually: 1/(1+φ) = 2/(3+√5) and (3-√5)/2, so need:
  -- 2/(3+√5) = (3-√5)/2 iff 4 = (3-√5)(3+√5) = 9 - 5 = 4. ✓
  nlinarith [sqrt5_sq]

/-- Key relationship: when x ≥ length1 + length2, we have c = 2x - 1 ≥ 2 - √5. -/
lemma interval2_c_lower_bound (x : ℝ) (hx : length1 + length2 ≤ x) :
    2 - Real.sqrt 5 ≤ 2 * x - 1 := by
  rw [length12_eq_sqrt5] at hx
  linarith

/-- Helper: segmentPoint expressed in terms of E. -/
lemma segmentPoint_eq_smul_E (x : ℝ) : segmentPoint x = (2 * x - 1) • E := by
  unfold segmentPoint E'
  rw [sub_neg_eq_add, show E + E = (2 : ℝ) • E by simp [two_smul], smul_smul]
  rw [show -E + (x * 2) • E = (x * 2 - 1) • E by rw [sub_smul, one_smul]; ring_nf]
  congr 1; ring

/-- Helper: translation property of segmentPoint. -/
lemma segmentPoint_add_displacement (x d : ℝ) :
    segmentPoint (x + d) = segmentPoint x + (2 * d) • E := by
  rw [segmentPoint_eq_smul_E, segmentPoint_eq_smul_E]
  simp only [Complex.real_smul]
  rw [← add_mul]
  congr 1
  push_cast
  ring

end TDCSG.CompoundSymmetry.GG5
