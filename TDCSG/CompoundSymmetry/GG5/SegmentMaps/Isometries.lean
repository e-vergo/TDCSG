/-
Copyright (c) 2025-10-18. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

import TDCSG.CompoundSymmetry.GG5.SegmentMaps.Maps

/-!
# GG5 Isometry Properties

This file proves that map1, map2, map3 are isometries on the lens intersection
and that their translation lengths are irrationally related.

## Main Results

- `maps_are_isometries_on_intersection`: The three transformations preserve
  distances on the disk intersection
- `translation_lengths_irrational`: Translation lengths are not rationally
  related to segment length

## Implementation Notes

The isometry proofs proceed by careful composition analysis, tracking that each
point and its image remain in the appropriate disk regions through each step of
the transformation chain.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real

/-! ### Global Isometry Properties -/

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

/-! ### Translation Length Irrationality -/

/--
Translation lengths are not rationally related to segment length.
-/
theorem translation_lengths_irrational :
    ∀ (p q : ℤ), p ≠ 0 ∨ q ≠ 0 →
    (p : ℝ) * translation_length_1 + (q : ℝ) *
      translation_length_2 ≠ 0 := by
  intro p q hpq
  exact translations_irrational p q hpq

end TDCSG.CompoundSymmetry.GG5
