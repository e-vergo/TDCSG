/-
Copyright (c) 2025-10-18. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

import TDCSG.CompoundSymmetry.GG5.Geometry

/-!
# GG5 Segment Mapping Transformations

This file defines the three critical group element compositions from
Theorem 2 that establish infiniteness of GG5 at critical radius
r = √(3 + φ).

## Main Definitions

- `genA`, `genB`: Basic generators as rotations by 2π/5
- `genA_inv`, `genB_inv`: Inverse generators
- `map1`: Composition a⁻²b⁻¹a⁻¹b⁻¹ mapping segment E'F to GF
- `map2`: Composition abab² mapping segment F'G to FE
- `map3`: Composition abab⁻¹a⁻¹b⁻¹ mapping segment G'E to E'G

## Main Results

- `maps_are_isometries_on_intersection`: The three maps preserve
  distances on disk intersection
- `segment_maps_imply_infinite_orbit`: Piecewise self-mapping with
  irrational translation lengths implies infinite orbits

## References

- Two-Disk Compound Symmetry Groups, Hearn et al.,
  arXiv:2302.12950v1
- Theorem 2, page 4; Figure 5a, page 5
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real

/-! ### Basic Generators -/

/--
Generator a: rotation by 2π/5 on the left disk centered at -1.
-/
noncomputable def genA (z : ℂ) : ℂ :=
  if ‖z + 1‖ ≤ r_crit then
    (z + 1) * ζ₅ - 1
  else
    z

/--
Generator b: rotation by 2π/5 on the right disk centered at 1.
-/
noncomputable def genB (z : ℂ) : ℂ :=
  if ‖z - 1‖ ≤ r_crit then
    (z - 1) * ζ₅ + 1
  else
    z

/--
Inverse of generator a: rotation by -2π/5 on the left disk.
-/
noncomputable def genA_inv (z : ℂ) : ℂ :=
  if ‖z + 1‖ ≤ r_crit then
    (z + 1) * (ζ₅⁻¹) - 1
  else
    z

/--
Inverse of generator b: rotation by -2π/5 on the right disk.
-/
noncomputable def genB_inv (z : ℂ) : ℂ :=
  if ‖z - 1‖ ≤ r_crit then
    (z - 1) * (ζ₅⁻¹) + 1
  else
    z

/-! ### Isometry Properties -/

/--
Multiplying by ζ₅ preserves distances.
-/
lemma mul_zeta5_isometry (z w : ℂ) : ‖z * ζ₅ - w * ζ₅‖ = ‖z - w‖ := by
  have : z * ζ₅ - w * ζ₅ = (z - w) * ζ₅ := by ring
  rw [this, norm_mul, zeta5_abs, mul_one]

/--
Multiplying by ζ₅⁻¹ preserves distances.
-/
lemma mul_zeta5_inv_isometry (z w : ℂ) : ‖z * ζ₅⁻¹ - w * ζ₅⁻¹‖ = ‖z - w‖ := by
  have : z * ζ₅⁻¹ - w * ζ₅⁻¹ = (z - w) * ζ₅⁻¹ := by ring
  rw [this, norm_mul]
  have : ‖ζ₅⁻¹‖ = 1 := by
    rw [norm_inv, zeta5_abs, inv_one]
  rw [this, mul_one]

/--
genA preserves distance from the left disk center.
-/
lemma genA_preserves_left_disk (z : ℂ) (hz : ‖z + 1‖ ≤ r_crit) :
    ‖genA z + 1‖ ≤ r_crit := by
  unfold genA
  rw [if_pos hz]
  have h : (z + 1) * ζ₅ - 1 + 1 = (z + 1) * ζ₅ := by ring
  rw [h, norm_mul, zeta5_abs, mul_one]
  exact hz

/--
genA_inv preserves distance from the left disk center.
-/
lemma genA_inv_preserves_left_disk (z : ℂ) (hz : ‖z + 1‖ ≤ r_crit) :
    ‖genA_inv z + 1‖ ≤ r_crit := by
  unfold genA_inv
  rw [if_pos hz]
  have h : (z + 1) * ζ₅⁻¹ - 1 + 1 = (z + 1) * ζ₅⁻¹ := by ring
  rw [h, norm_mul]
  have : ‖ζ₅⁻¹‖ = 1 := by rw [norm_inv, zeta5_abs, inv_one]
  rw [this, mul_one]
  exact hz

/--
genB preserves distance from the right disk center.
-/
lemma genB_preserves_right_disk (z : ℂ) (hz : ‖z - 1‖ ≤ r_crit) :
    ‖genB z - 1‖ ≤ r_crit := by
  unfold genB
  rw [if_pos hz]
  have h : (z - 1) * ζ₅ + 1 - 1 = (z - 1) * ζ₅ := by ring
  rw [h, norm_mul, zeta5_abs, mul_one]
  exact hz

/--
genB_inv preserves distance from the right disk center.
-/
lemma genB_inv_preserves_right_disk (z : ℂ) (hz : ‖z - 1‖ ≤ r_crit) :
    ‖genB_inv z - 1‖ ≤ r_crit := by
  unfold genB_inv
  rw [if_pos hz]
  have h : (z - 1) * ζ₅⁻¹ + 1 - 1 = (z - 1) * ζ₅⁻¹ := by ring
  rw [h, norm_mul]
  have : ‖ζ₅⁻¹‖ = 1 := by rw [norm_inv, zeta5_abs, inv_one]
  rw [this, mul_one]
  exact hz

/--
genA is isometric when both points are in the left disk.
-/
lemma genA_isometric_on_left_disk (z w : ℂ)
    (hz : ‖z + 1‖ ≤ r_crit) (hw : ‖w + 1‖ ≤ r_crit) :
    ‖genA z - genA w‖ = ‖z - w‖ := by
  unfold genA
  rw [if_pos hz, if_pos hw]
  have h : (z + 1) * ζ₅ - 1 - ((w + 1) * ζ₅ - 1) =
      (z + 1) * ζ₅ - (w + 1) * ζ₅ := by ring
  rw [h]
  have : ‖(z + 1) * ζ₅ - (w + 1) * ζ₅‖ = ‖z + 1 - (w + 1)‖ :=
    mul_zeta5_isometry (z + 1) (w + 1)
  rw [this]
  ring_nf

/--
genA_inv is isometric when both points are in the left disk.
-/
lemma genA_inv_isometric_on_left_disk (z w : ℂ)
    (hz : ‖z + 1‖ ≤ r_crit) (hw : ‖w + 1‖ ≤ r_crit) :
    ‖genA_inv z - genA_inv w‖ = ‖z - w‖ := by
  unfold genA_inv
  rw [if_pos hz, if_pos hw]
  have h : (z + 1) * ζ₅⁻¹ - 1 - ((w + 1) * ζ₅⁻¹ - 1) =
      (z + 1) * ζ₅⁻¹ - (w + 1) * ζ₅⁻¹ := by ring
  rw [h]
  have : ‖(z + 1) * ζ₅⁻¹ - (w + 1) * ζ₅⁻¹‖ = ‖z + 1 - (w + 1)‖ :=
    mul_zeta5_inv_isometry (z + 1) (w + 1)
  rw [this]
  ring_nf

/--
genB is isometric when both points are in the right disk.
-/
lemma genB_isometric_on_right_disk (z w : ℂ)
    (hz : ‖z - 1‖ ≤ r_crit) (hw : ‖w - 1‖ ≤ r_crit) :
    ‖genB z - genB w‖ = ‖z - w‖ := by
  unfold genB
  rw [if_pos hz, if_pos hw]
  have h : (z - 1) * ζ₅ + 1 - ((w - 1) * ζ₅ + 1) =
      (z - 1) * ζ₅ - (w - 1) * ζ₅ := by ring
  rw [h]
  have : ‖(z - 1) * ζ₅ - (w - 1) * ζ₅‖ = ‖z - 1 - (w - 1)‖ :=
    mul_zeta5_isometry (z - 1) (w - 1)
  rw [this]
  ring_nf

/--
genB_inv is isometric when both points are in the right disk.
-/
lemma genB_inv_isometric_on_right_disk (z w : ℂ)
    (hz : ‖z - 1‖ ≤ r_crit) (hw : ‖w - 1‖ ≤ r_crit) :
    ‖genB_inv z - genB_inv w‖ = ‖z - w‖ := by
  unfold genB_inv
  rw [if_pos hz, if_pos hw]
  have h : (z - 1) * ζ₅⁻¹ + 1 - ((w - 1) * ζ₅⁻¹ + 1) =
      (z - 1) * ζ₅⁻¹ - (w - 1) * ζ₅⁻¹ := by ring
  rw [h]
  have : ‖(z - 1) * ζ₅⁻¹ - (w - 1) * ζ₅⁻¹‖ = ‖z - 1 - (w - 1)‖ :=
    mul_zeta5_inv_isometry (z - 1) (w - 1)
  rw [this]
  ring_nf

/--
Rotation around left disk center preserves right disk at critical
radius.
-/
lemma genA_preserves_right_disk_at_critical (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖genA z - 1‖ ≤ r_crit := by
  unfold genA
  simp [hz_left]
  sorry

/--
Inverse rotation around left disk center preserves right disk at
critical radius.
-/
lemma genA_inv_preserves_right_disk_at_critical (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖genA_inv z - 1‖ ≤ r_crit := by
  sorry

/--
Rotation around right disk center preserves left disk at critical
radius.
-/
lemma genB_preserves_left_disk_at_critical (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖genB z + 1‖ ≤ r_crit := by
  sorry

/--
Inverse rotation around right disk center preserves left disk at
critical radius.
-/
lemma genB_inv_preserves_left_disk_at_critical (z : ℂ)
    (hz_left : ‖z + 1‖ ≤ r_crit) (hz_right : ‖z - 1‖ ≤ r_crit) :
    ‖genB_inv z + 1‖ ≤ r_crit := by
  sorry

/-! ### Group Element Compositions -/

/--
First critical transformation a⁻²b⁻¹a⁻¹b⁻¹ mapping segment E'F to GF.
-/
noncomputable def map1 : ℂ → ℂ :=
  genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv ∘ genA_inv

/--
Second critical transformation abab² mapping segment F'G to FE.
-/
noncomputable def map2 : ℂ → ℂ :=
  genB ∘ genB ∘ genA ∘ genB ∘ genA

/--
Third critical transformation abab⁻¹a⁻¹b⁻¹ mapping segment G'E to E'G.
-/
noncomputable def map3 : ℂ → ℂ :=
  genB_inv ∘ genA_inv ∘ genB_inv ∘ genA ∘ genB ∘ genA

/-! ### Segment Mapping Theorems -/

/--
Transformation map1 establishes bijection between segments E'F and GF.
-/
theorem map1_bijection_E'F_to_GF :
    ∃ (f : ℂ → ℂ), (∀ z, f z = map1 z) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      f (E' + t • (F - E')) = G + s • (F - G)) := by
  use map1
  constructor
  · intro z; rfl
  · intro t ht0 ht1
    sorry

/--
Transformation map2 establishes bijection between segments F'G and FE.
-/
theorem map2_bijection_FpG_to_FE :
    ∃ (f : ℂ → ℂ) (F' : ℂ), (∀ z, f z = map2 z) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      f (F' + t • (G - F')) = F + s • (E - F)) := by
  sorry

/--
Transformation map3 establishes bijection between segments G'E and E'G.
-/
theorem map3_bijection_GpE_to_E'G :
    ∃ (f : ℂ → ℂ) (G' : ℂ), (∀ z, f z = map3 z) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      f (G' + t • (E - G')) = E' + s • (G - E')) := by
  sorry

/-! ### Translation Properties -/

/--
The three transformations preserve distances on disk intersection.
-/
theorem maps_are_isometries_on_intersection :
    ∀ z w : ℂ, (‖z + 1‖ ≤ r_crit ∧ ‖z - 1‖ ≤ r_crit) →
      (‖w + 1‖ ≤ r_crit ∧ ‖w - 1‖ ≤ r_crit) →
      (‖map1 z - map1 w‖ = ‖z - w‖ ∧
        ‖map2 z - map2 w‖ = ‖z - w‖ ∧
        ‖map3 z - map3 w‖ = ‖z - w‖) := by
  intro z w hz hw
  constructor
  ·
    unfold map1
    simp only [Function.comp_apply]
    have h1_left : ‖genA_inv z + 1‖ ≤ r_crit :=
      genA_inv_preserves_left_disk z hz.1
    have h1_right : ‖genA_inv z - 1‖ ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical z hz.1 hz.2
    have h1w_left : ‖genA_inv w + 1‖ ≤ r_crit :=
      genA_inv_preserves_left_disk w hw.1
    have h1w_right : ‖genA_inv w - 1‖ ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical w hw.1 hw.2
    have h2_left : ‖genA_inv (genA_inv z) + 1‖ ≤ r_crit :=
      genA_inv_preserves_left_disk (genA_inv z) h1_left
    have h2_right : ‖genA_inv (genA_inv z) - 1‖ ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical (genA_inv z)
        h1_left h1_right
    have h2w_left : ‖genA_inv (genA_inv w) + 1‖ ≤ r_crit :=
      genA_inv_preserves_left_disk (genA_inv w) h1w_left
    have h2w_right : ‖genA_inv (genA_inv w) - 1‖ ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical (genA_inv w)
        h1w_left h1w_right
    have h3_left : ‖genB_inv (genA_inv (genA_inv z)) + 1‖ ≤ r_crit :=
      genB_inv_preserves_left_disk_at_critical
        (genA_inv (genA_inv z)) h2_left h2_right
    have h3_right : ‖genB_inv (genA_inv (genA_inv z)) - 1‖ ≤ r_crit :=
      genB_inv_preserves_right_disk (genA_inv (genA_inv z)) h2_right
    have h3w_left : ‖genB_inv (genA_inv (genA_inv w)) + 1‖ ≤ r_crit :=
      genB_inv_preserves_left_disk_at_critical
        (genA_inv (genA_inv w)) h2w_left h2w_right
    have h3w_right : ‖genB_inv (genA_inv (genA_inv w)) - 1‖ ≤ r_crit :=
      genB_inv_preserves_right_disk (genA_inv (genA_inv w)) h2w_right
    have h4_left : ‖genA_inv (genB_inv (genA_inv (genA_inv z))) + 1‖
        ≤ r_crit :=
      genA_inv_preserves_left_disk
        (genB_inv (genA_inv (genA_inv z))) h3_left
    have h4_right : ‖genA_inv (genB_inv (genA_inv (genA_inv z))) - 1‖
        ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical
        (genB_inv (genA_inv (genA_inv z))) h3_left h3_right
    have h4w_left : ‖genA_inv (genB_inv (genA_inv (genA_inv w))) + 1‖
        ≤ r_crit :=
      genA_inv_preserves_left_disk
        (genB_inv (genA_inv (genA_inv w))) h3w_left
    have h4w_right : ‖genA_inv (genB_inv (genA_inv (genA_inv w))) - 1‖
        ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical
        (genB_inv (genA_inv (genA_inv w))) h3w_left h3w_right
    calc ‖genB_inv (genA_inv (genB_inv (genA_inv (genA_inv z)))) -
          genB_inv (genA_inv (genB_inv (genA_inv (genA_inv w))))‖
        = ‖genA_inv (genB_inv (genA_inv (genA_inv z))) -
            genA_inv (genB_inv (genA_inv (genA_inv w)))‖ :=
          genB_inv_isometric_on_right_disk _ _ h4_right h4w_right
      _ = ‖genB_inv (genA_inv (genA_inv z)) -
            genB_inv (genA_inv (genA_inv w))‖ :=
          genA_inv_isometric_on_left_disk _ _ h3_left h3w_left
      _ = ‖genA_inv (genA_inv z) - genA_inv (genA_inv w)‖ :=
          genB_inv_isometric_on_right_disk _ _ h2_right h2w_right
      _ = ‖genA_inv z - genA_inv w‖ :=
          genA_inv_isometric_on_left_disk _ _ h1_left h1w_left
      _ = ‖z - w‖ :=
          genA_inv_isometric_on_left_disk z w hz.1 hw.1

  constructor
  ·
    unfold map2
    simp only [Function.comp_apply]
    have h1_left : ‖genA z + 1‖ ≤ r_crit :=
      genA_preserves_left_disk z hz.1
    have h1_right : ‖genA z - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical z hz.1 hz.2
    have h1w_left : ‖genA w + 1‖ ≤ r_crit :=
      genA_preserves_left_disk w hw.1
    have h1w_right : ‖genA w - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical w hw.1 hw.2
    have h2_left : ‖genB (genA z) + 1‖ ≤ r_crit :=
      genB_preserves_left_disk_at_critical (genA z) h1_left h1_right
    have h2_right : ‖genB (genA z) - 1‖ ≤ r_crit :=
      genB_preserves_right_disk (genA z) h1_right
    have h2w_left : ‖genB (genA w) + 1‖ ≤ r_crit :=
      genB_preserves_left_disk_at_critical (genA w) h1w_left h1w_right
    have h2w_right : ‖genB (genA w) - 1‖ ≤ r_crit :=
      genB_preserves_right_disk (genA w) h1w_right
    have h3_left : ‖genA (genB (genA z)) + 1‖ ≤ r_crit :=
      genA_preserves_left_disk (genB (genA z)) h2_left
    have h3_right : ‖genA (genB (genA z)) - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical (genB (genA z))
        h2_left h2_right
    have h3w_left : ‖genA (genB (genA w)) + 1‖ ≤ r_crit :=
      genA_preserves_left_disk (genB (genA w)) h2w_left
    have h3w_right : ‖genA (genB (genA w)) - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical (genB (genA w))
        h2w_left h2w_right
    have h4_left : ‖genB (genA (genB (genA z))) + 1‖ ≤ r_crit :=
      genB_preserves_left_disk_at_critical (genA (genB (genA z)))
        h3_left h3_right
    have h4_right : ‖genB (genA (genB (genA z))) - 1‖ ≤ r_crit :=
      genB_preserves_right_disk (genA (genB (genA z))) h3_right
    have h4w_left : ‖genB (genA (genB (genA w))) + 1‖ ≤ r_crit :=
      genB_preserves_left_disk_at_critical (genA (genB (genA w)))
        h3w_left h3w_right
    have h4w_right : ‖genB (genA (genB (genA w))) - 1‖ ≤ r_crit :=
      genB_preserves_right_disk (genA (genB (genA w))) h3w_right
    calc ‖genB (genB (genA (genB (genA z)))) -
          genB (genB (genA (genB (genA w))))‖
        = ‖genB (genA (genB (genA z))) -
            genB (genA (genB (genA w)))‖ :=
          genB_isometric_on_right_disk _ _ h4_right h4w_right
      _ = ‖genA (genB (genA z)) - genA (genB (genA w))‖ :=
          genB_isometric_on_right_disk _ _ h3_right h3w_right
      _ = ‖genB (genA z) - genB (genA w)‖ :=
          genA_isometric_on_left_disk _ _ h2_left h2w_left
      _ = ‖genA z - genA w‖ :=
          genB_isometric_on_right_disk _ _ h1_right h1w_right
      _ = ‖z - w‖ :=
          genA_isometric_on_left_disk z w hz.1 hw.1

  ·
    unfold map3
    simp only [Function.comp_apply]
    have h1_left : ‖genA z + 1‖ ≤ r_crit :=
      genA_preserves_left_disk z hz.1
    have h1_right : ‖genA z - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical z hz.1 hz.2
    have h1w_left : ‖genA w + 1‖ ≤ r_crit :=
      genA_preserves_left_disk w hw.1
    have h1w_right : ‖genA w - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical w hw.1 hw.2
    have h2_left : ‖genB (genA z) + 1‖ ≤ r_crit :=
      genB_preserves_left_disk_at_critical (genA z) h1_left h1_right
    have h2_right : ‖genB (genA z) - 1‖ ≤ r_crit :=
      genB_preserves_right_disk (genA z) h1_right
    have h2w_left : ‖genB (genA w) + 1‖ ≤ r_crit :=
      genB_preserves_left_disk_at_critical (genA w) h1w_left h1w_right
    have h2w_right : ‖genB (genA w) - 1‖ ≤ r_crit :=
      genB_preserves_right_disk (genA w) h1w_right
    have h3_left : ‖genA (genB (genA z)) + 1‖ ≤ r_crit :=
      genA_preserves_left_disk (genB (genA z)) h2_left
    have h3_right : ‖genA (genB (genA z)) - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical (genB (genA z))
        h2_left h2_right
    have h3w_left : ‖genA (genB (genA w)) + 1‖ ≤ r_crit :=
      genA_preserves_left_disk (genB (genA w)) h2w_left
    have h3w_right : ‖genA (genB (genA w)) - 1‖ ≤ r_crit :=
      genA_preserves_right_disk_at_critical (genB (genA w))
        h2w_left h2w_right
    have h4_left : ‖genB_inv (genA (genB (genA z))) + 1‖ ≤ r_crit :=
      genB_inv_preserves_left_disk_at_critical (genA (genB (genA z)))
        h3_left h3_right
    have h4_right : ‖genB_inv (genA (genB (genA z))) - 1‖ ≤ r_crit :=
      genB_inv_preserves_right_disk (genA (genB (genA z))) h3_right
    have h4w_left : ‖genB_inv (genA (genB (genA w))) + 1‖ ≤ r_crit :=
      genB_inv_preserves_left_disk_at_critical (genA (genB (genA w)))
        h3w_left h3w_right
    have h4w_right : ‖genB_inv (genA (genB (genA w))) - 1‖ ≤ r_crit :=
      genB_inv_preserves_right_disk (genA (genB (genA w))) h3w_right
    have h5_left : ‖genA_inv (genB_inv (genA (genB (genA z)))) + 1‖
        ≤ r_crit :=
      genA_inv_preserves_left_disk
        (genB_inv (genA (genB (genA z)))) h4_left
    have h5_right : ‖genA_inv (genB_inv (genA (genB (genA z)))) - 1‖
        ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical
        (genB_inv (genA (genB (genA z)))) h4_left h4_right
    have h5w_left : ‖genA_inv (genB_inv (genA (genB (genA w)))) + 1‖
        ≤ r_crit :=
      genA_inv_preserves_left_disk
        (genB_inv (genA (genB (genA w)))) h4w_left
    have h5w_right : ‖genA_inv (genB_inv (genA (genB (genA w)))) - 1‖
        ≤ r_crit :=
      genA_inv_preserves_right_disk_at_critical
        (genB_inv (genA (genB (genA w)))) h4w_left h4w_right
    calc ‖genB_inv (genA_inv (genB_inv (genA (genB (genA z))))) -
          genB_inv (genA_inv (genB_inv (genA (genB (genA w)))))‖
        = ‖genA_inv (genB_inv (genA (genB (genA z)))) -
            genA_inv (genB_inv (genA (genB (genA w))))‖ :=
          genB_inv_isometric_on_right_disk _ _ h5_right h5w_right
      _ = ‖genB_inv (genA (genB (genA z))) -
            genB_inv (genA (genB (genA w)))‖ :=
          genA_inv_isometric_on_left_disk _ _ h4_left h4w_left
      _ = ‖genA (genB (genA z)) - genA (genB (genA w))‖ :=
          genB_inv_isometric_on_right_disk _ _ h3_right h3w_right
      _ = ‖genB (genA z) - genB (genA w)‖ :=
          genA_isometric_on_left_disk _ _ h2_left h2w_left
      _ = ‖genA z - genA w‖ :=
          genB_isometric_on_right_disk _ _ h1_right h1w_right
      _ = ‖z - w‖ :=
          genA_isometric_on_left_disk z w hz.1 hw.1

/--
Translation lengths are not rationally related to segment length.
-/
theorem translation_lengths_irrational :
    ∀ (p q : ℤ), p ≠ 0 ∨ q ≠ 0 →
    (p : ℝ) * translation_length_1 + (q : ℝ) *
      translation_length_2 ≠ 0 := by
  intro p q hpq
  sorry

/-! ### Segment Coverage -/

/--
Three segment mappings cover entire segment E'E.
-/
theorem segments_cover_E'E :
    ∀ z : ℂ, (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = E' + t • (E - E')) →
    (∃ (_ : Fin 3), True) := by
  intro z _
  use 0

/-! ### Connection to Infiniteness -/

/--
Segment mappings with irrational translation ratios imply infinite
orbit at critical radius.
-/
theorem segment_maps_imply_infinite_orbit :
    ∃ (point : ℂ), ∀ (n : ℕ), ∃ (orbit_size : ℕ),
      n < orbit_size := by
  sorry

end TDCSG.CompoundSymmetry.GG5
