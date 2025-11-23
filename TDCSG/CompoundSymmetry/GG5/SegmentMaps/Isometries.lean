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
  -- Both z and w are in the disk intersection, so they're in both disks
  have hz_left := hz.1
  have hz_right := hz.2
  have hw_left := hw.1
  have hw_right := hw.2

  constructor
  · -- Prove map1 is an isometry on intersection
    -- map1 = genB ∘ genA ∘ genB ∘ genA ∘ genA
    -- Strategy: z,w start in intersection. Generators preserve intersection,
    -- and are isometric on intersection. Chain through 5 applications.
    unfold map1
    simp only [Function.comp_apply]

    -- Apply generators one by one, using isometry on intersection
    calc ‖genB (genA (genB (genA (genA z)))) -
           genB (genA (genB (genA (genA w))))‖
        = ‖genA (genB (genA (genA z))) -
            genA (genB (genA (genA w)))‖ := by
          apply genB_isometric_on_intersection
          · apply genA_preserves_intersection
            apply genB_preserves_intersection
            apply genA_preserves_intersection
            apply genA_preserves_intersection
            exact hz
          · apply genA_preserves_intersection
            apply genB_preserves_intersection
            apply genA_preserves_intersection
            apply genA_preserves_intersection
            exact hw
      _ = ‖genB (genA (genA z)) -
            genB (genA (genA w))‖ := by
          apply genA_isometric_on_intersection
          · apply genB_preserves_intersection
            apply genA_preserves_intersection
            apply genA_preserves_intersection
            exact hz
          · apply genB_preserves_intersection
            apply genA_preserves_intersection
            apply genA_preserves_intersection
            exact hw
      _ = ‖genA (genA z) - genA (genA w)‖ := by
          apply genB_isometric_on_intersection
          · apply genA_preserves_intersection
            apply genA_preserves_intersection
            exact hz
          · apply genA_preserves_intersection
            apply genA_preserves_intersection
            exact hw
      _ = ‖genA z - genA w‖ := by
          apply genA_isometric_on_intersection
          · apply genA_preserves_intersection; exact hz
          · apply genA_preserves_intersection; exact hw
      _ = ‖z - w‖ := genA_isometric_on_intersection z w hz hw

  constructor
  · -- Prove map2 is an isometry
    -- map2 = genB_inv ∘ genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv
    unfold map2
    simp only [Function.comp_apply]
    calc ‖genB_inv (genB_inv (genA_inv (genB_inv (genA_inv z)))) -
           genB_inv (genB_inv (genA_inv (genB_inv (genA_inv w))))‖
        = ‖genB_inv (genA_inv (genB_inv (genA_inv z))) -
            genB_inv (genA_inv (genB_inv (genA_inv w)))‖ := by
          apply genB_inv_isometric_on_intersection
          · apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genA_inv (genB_inv (genA_inv z)) -
            genA_inv (genB_inv (genA_inv w))‖ := by
          apply genB_inv_isometric_on_intersection
          · apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genB_inv (genA_inv z) - genB_inv (genA_inv w)‖ := by
          apply genA_inv_isometric_on_intersection
          · apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genA_inv z - genA_inv w‖ := by
          apply genB_inv_isometric_on_intersection
          · apply genA_inv_preserves_intersection; exact hz
          · apply genA_inv_preserves_intersection; exact hw
      _ = ‖z - w‖ := genA_inv_isometric_on_intersection z w hz hw

  · -- Prove map3 is an isometry
    -- map3 = genB ∘ genA ∘ genB ∘ genA_inv ∘ genB_inv ∘ genA_inv
    unfold map3
    simp only [Function.comp_apply]
    calc ‖genB (genA (genB (genA_inv (genB_inv (genA_inv z))))) -
           genB (genA (genB (genA_inv (genB_inv (genA_inv w)))))‖
        = ‖genA (genB (genA_inv (genB_inv (genA_inv z)))) -
            genA (genB (genA_inv (genB_inv (genA_inv w))))‖ := by
          apply genB_isometric_on_intersection
          · apply genA_preserves_intersection
            apply genB_preserves_intersection
            apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genA_preserves_intersection
            apply genB_preserves_intersection
            apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genB (genA_inv (genB_inv (genA_inv z))) -
            genB (genA_inv (genB_inv (genA_inv w)))‖ := by
          apply genA_isometric_on_intersection
          · apply genB_preserves_intersection
            apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genB_preserves_intersection
            apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genA_inv (genB_inv (genA_inv z)) -
            genA_inv (genB_inv (genA_inv w))‖ := by
          apply genB_isometric_on_intersection
          · apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genA_inv_preserves_intersection
            apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genB_inv (genA_inv z) - genB_inv (genA_inv w)‖ := by
          apply genA_inv_isometric_on_intersection
          · apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hz
          · apply genB_inv_preserves_intersection
            apply genA_inv_preserves_intersection
            exact hw
      _ = ‖genA_inv z - genA_inv w‖ := by
          apply genB_inv_isometric_on_intersection
          · apply genA_inv_preserves_intersection; exact hz
          · apply genA_inv_preserves_intersection; exact hw
      _ = ‖z - w‖ := genA_inv_isometric_on_intersection z w hz hw

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
