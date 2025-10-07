import TDCSG.TwoDisk.GG5Geometry

/-!
# Theorem 2: GG₅ is Infinite at Critical Radius

This file contains the main result: GG₅ is infinite at r = √(3 + φ).

## Main theorem

* `theorem2`: GG₅(√(3 + φ)) is infinite

## Proof strategy

1. Define three group element sequences that act as piecewise translations
2. Show they map line segment E'E onto itself with irrational translation lengths
3. Conclude the origin has an infinite orbit

## References

* Theorem 2 in "Two-Disk Compound Symmetry Groups" (lines 170-187)
-/

open Complex Real

namespace TwoDiskSystem

/-- Build the specific GG₅ system at critical radius. -/
noncomputable def GG5_critical : TwoDiskSystem where
  n₁ := 5
  n₂ := 5
  r₁ := r_c
  r₂ := r_c
  n₁_pos := by norm_num
  n₂_pos := by norm_num
  r₁_pos := r_c_pos
  r₂_pos := r_c_pos

/-- Case 1: The sequence a⁻²b⁻¹a⁻¹b⁻¹ maps segment E'F' to segment GF. -/
theorem case1_transformation :
    let sys := GG5_critical
    let g := (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ *
             (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹
    ∀ z : ℂ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      z = E' + t • (F' - E') →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
        applyGroupElement sys g z = G + s • (F - G) := by
  -- This is a specific geometric fact about the GG₅ system at critical radius
  -- The proof would require computing the exact transformation of the segment
  sorry

/-- Case 2: The sequence abab² maps segment F'G' to segment FE. -/
theorem case2_transformation :
    let sys := GG5_critical
    let g := FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
             (FreeGroup.of 1) * (FreeGroup.of 1)
    ∀ z : ℂ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      z = F' + t • (G' - F') →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
        applyGroupElement sys g z = F + s • (E - F) := by
  -- This is a specific geometric fact about the GG₅ system at critical radius
  sorry

/-- Case 3: The sequence abab⁻¹a⁻¹b⁻¹ maps segment G'E to segment E'G. -/
theorem case3_transformation :
    let sys := GG5_critical
    let g := FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
             (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹
    ∀ z : ℂ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      z = G' + t • (E - G') →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
        applyGroupElement sys g z = E' + s • (G - E') := by
  -- This is a specific geometric fact about the GG₅ system at critical radius
  sorry

/-- All three transformations keep points within the disk intersection. -/
theorem transformations_stay_in_intersection :
    let sys := GG5_critical
    let g1 := (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ *
              (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹
    let g2 := FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
              (FreeGroup.of 1) * (FreeGroup.of 1)
    let g3 := FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
              (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹
    ∀ z ∈ sys.diskIntersection, ∀ g ∈ [g1, g2, g3],
      applyGroupElement sys g z ∈ sys.diskIntersection := by
  -- This requires showing that for the specific critical radius and these specific
  -- group elements, points in the intersection remain in the intersection
  -- This is a geometric property that follows from the critical radius constraint
  sorry  -- Requires detailed geometric analysis of how these specific transformations
         -- preserve the intersection at the critical radius

/-- The three operations allow arbitrary movement along E'E. -/
theorem can_move_arbitrarily_on_segment :
    let sys := GG5_critical
    ∀ ε > 0, ∀ target : ℂ,
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ target = E' + t • (E - E')) →
      ∃ g : TwoDiskGroup, ‖applyGroupElement sys g 0 - target‖ < ε := by
  sorry

/-- The origin has an infinite orbit. -/
theorem origin_infinite_orbit : Set.Infinite (orbit GG5_critical 0) := by
  -- The key insight: the three transformations create dense orbits on E'E
  -- Since the translation ratios involve φ (irrational), the orbit is dense
  -- and therefore infinite

  -- We use the fact that the transformations have irrational ratios
  -- This is a fundamental consequence of translations_irrational_ratio
  -- Combined with the density argument, this implies infinitude

  -- The proof would require:
  -- 1. Showing the transformations act as piecewise translations
  -- 2. Using the irrational ratio from translations_irrational_ratio
  -- 3. Applying a density argument to show infinite orbits
  sorry

/-- Theorem 2: GG₅ is infinite at r = √(3 + φ). -/
theorem theorem2 : GG5_critical.IsInfiniteGroup := by
  unfold IsInfiniteGroup
  use 0
  exact origin_infinite_orbit

end TwoDiskSystem
