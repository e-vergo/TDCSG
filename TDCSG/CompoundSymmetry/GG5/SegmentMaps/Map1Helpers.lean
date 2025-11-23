/-
Helper lemmas for map1 endpoint proofs.
These are intermediate computation steps for map1 = genB ∘ genA ∘ genB ∘ genA ∘ genA.
-/

import TDCSG.CompoundSymmetry.GG5.SegmentMaps.Maps

namespace TDCSG.CompoundSymmetry.GG5

open Complex

/-- Intermediate computation for map1 E' step 2 -/
private lemma map1_E'_step2_simp : ζ₅^4 - ζ₅^3 + ζ₅^2 - 1 = -2 - ζ₅ - 2*ζ₅^3 := by
  have h4 := zeta5_pow4_eq
  calc ζ₅^4 - ζ₅^3 + ζ₅^2 - 1
      = (-1 - ζ₅ - ζ₅^2 - ζ₅^3) - ζ₅^3 + ζ₅^2 - 1 := by rw [h4]
    _ = -2 - ζ₅ - 2*ζ₅^3 := by ring

/-- Intermediate computation for map1 E' step 3 -/
private lemma map1_E'_step3_simp : ζ₅^5 - ζ₅^4 + ζ₅^3 - 2*ζ₅ + 1 = 3 - ζ₅ + ζ₅^2 + 2*ζ₅^3 := by
  have h5 := zeta5_pow_five
  have h4 := zeta5_pow4_eq
  calc ζ₅^5 - ζ₅^4 + ζ₅^3 - 2*ζ₅ + 1
      = 1 - (-1 - ζ₅ - ζ₅^2 - ζ₅^3) + ζ₅^3 - 2*ζ₅ + 1 := by rw [h5, h4]
    _ = 3 - ζ₅ + ζ₅^2 + 2*ζ₅^3 := by ring

/-- Intermediate computation for map1 E' step 4 -/
private lemma map1_E'_step4_simp : 4*ζ₅ - ζ₅^2 + ζ₅^3 + 2*ζ₅^4 - 1 = 2*ζ₅ - 3*ζ₅^2 - ζ₅^3 - 3 := by
  have h4 := zeta5_pow4_eq
  calc 4*ζ₅ - ζ₅^2 + ζ₅^3 + 2*ζ₅^4 - 1
      = 4*ζ₅ - ζ₅^2 + ζ₅^3 + 2*(-1 - ζ₅ - ζ₅^2 - ζ₅^3) - 1 := by rw [h4]
    _ = 2*ζ₅ - 3*ζ₅^2 - ζ₅^3 - 3 := by ring

/-- Intermediate computation for map1 E' step 5 -/
private lemma map1_E'_step5_simp : 2*ζ₅^2 - 3*ζ₅^3 - ζ₅^4 - 4*ζ₅ + 1 = 2 - 3*ζ₅ + 3*ζ₅^2 - 2*ζ₅^3 := by
  have h4 := zeta5_pow4_eq
  calc 2*ζ₅^2 - 3*ζ₅^3 - ζ₅^4 - 4*ζ₅ + 1
      = 2*ζ₅^2 - 3*ζ₅^3 - (-1 - ζ₅ - ζ₅^2 - ζ₅^3) - 4*ζ₅ + 1 := by rw [h4]
    _ = 2 - 3*ζ₅ + 3*ζ₅^2 - 2*ζ₅^3 := by ring

/-- G equals the simplified form -/
private lemma G_eq_simplified : G = 2 - 3*ζ₅ + 3*ζ₅^2 - 2*ζ₅^3 := by
  unfold G F E
  ring

/-- Intermediate computation for map1 F' step 1 -/
private lemma map1_F'_step1_simp : ζ₅^2 - ζ₅^3 + ζ₅^4 - 1 = -2 - ζ₅ - 2*ζ₅^3 := by
  have h4 := zeta5_pow4_eq
  calc ζ₅^2 - ζ₅^3 + ζ₅^4 - 1
      = ζ₅^2 - ζ₅^3 + (-1 - ζ₅ - ζ₅^2 - ζ₅^3) - 1 := by rw [h4]
    _ = -2 - ζ₅ - 2*ζ₅^3 := by ring

/-- Intermediate computation for map1 F' step 2 -/
private lemma map1_F'_step2_simp : -ζ₅ - ζ₅^2 - 2*ζ₅^4 - 1 = 1 + ζ₅ + ζ₅^2 + 2*ζ₅^3 := by
  have h4 := zeta5_pow4_eq
  calc -ζ₅ - ζ₅^2 - 2*ζ₅^4 - 1
      = -ζ₅ - ζ₅^2 - 2*(-1 - ζ₅ - ζ₅^2 - ζ₅^3) - 1 := by rw [h4]
    _ = 1 + ζ₅ + ζ₅^2 + 2*ζ₅^3 := by ring

/-- Intermediate computation for map1 F' step 3 -/
private lemma map1_F'_step3_simp : ζ₅^2 + ζ₅^3 + 2*ζ₅^4 + 1 = -1 - 2*ζ₅ - ζ₅^2 - ζ₅^3 := by
  have h4 := zeta5_pow4_eq
  calc ζ₅^2 + ζ₅^3 + 2*ζ₅^4 + 1
      = ζ₅^2 + ζ₅^3 + 2*(-1 - ζ₅ - ζ₅^2 - ζ₅^3) + 1 := by rw [h4]
    _ = -1 - 2*ζ₅ - ζ₅^2 - ζ₅^3 := by ring

/-- Intermediate computation for map1 F' step 4 -/
private lemma map1_F'_step4_simp : -2*ζ₅^2 - ζ₅^3 - ζ₅^4 - 1 = ζ₅ - ζ₅^2 := by
  have h4 := zeta5_pow4_eq
  calc -2*ζ₅^2 - ζ₅^3 - ζ₅^4 - 1
      = -2*ζ₅^2 - ζ₅^3 - (-1 - ζ₅ - ζ₅^2 - ζ₅^3) - 1 := by rw [h4]
    _ = ζ₅ - ζ₅^2 := by ring

/-- F equals the final simplified form -/
private lemma F_eq_final : F = 1 - ζ₅ + ζ₅^2 - ζ₅^3 := by unfold F; ring

end TDCSG.CompoundSymmetry.GG5
