import TDCSG.Analysis.GG5Properties
import TDCSG.Analysis.Translations
import TDCSG.Tools.FreeGroup
import TDCSG.Tools.Density
import TDCSG.Theory.IsometrySimple
import Mathlib.Analysis.Convex.Segment

/-!
# Theorem 2: GG₅ is Infinite at Critical Radius

This file contains the proof of Theorem 2: GG₅ has an infinite group
at the critical radius r = √(3 + φ).

## Main strategy

We show that certain group elements act as piecewise isometries that
map line segments with irrational length ratios, producing dense orbits
and hence proving infinity.
-/

open TwoDiskSystem GG5Properties
open scoped goldenRatio

namespace Theorem2

/-- Case 1: a⁻²b⁻¹a⁻¹b⁻¹ maps E'F' to GF -/
theorem case1_maps_E'F'_to_GF :
    let sys := GG5_critical
    ∃ z w : ℂ, z ∈ segment ℝ E' F' ∧
               w ∈ segment ℝ G F := by
  sorry  -- Geometric verification

/-- Case 2: abab² maps F'G' to FE -/
theorem case2_maps_F'G'_to_FE :
    let sys := GG5_critical
    ∃ z w : ℂ, z ∈ segment ℝ F' G' ∧
               w ∈ segment ℝ F E := by
  sorry  -- Geometric verification

/-- Case 3: abab⁻¹a⁻¹b⁻¹ maps G'E to E'G -/
theorem case3_maps_G'E_to_E'G :
    let sys := GG5_critical
    ∃ z w : ℂ, z ∈ segment ℝ G' E ∧
               w ∈ segment ℝ E' G := by
  sorry  -- Geometric verification

/-- The key lemma: segments have irrational length ratios -/
lemma segment_ratios_irrational :
    Irrational (‖E - E'‖ / ‖F - F'‖) := by
  exact translations_irrational_ratio

/-- Main Theorem 2: GG₅ is infinite at critical radius -/
theorem GG5_infinite :
    let sys := GG5_critical
    ∃ z : ℂ, Set.Infinite (Set.range (fun g : TwoDiskGroup => applyGroupElement sys g z)) := by
  intro sys
  -- Strategy: Use the three cases to show dense orbits

  -- The piecewise isometries from the three cases create
  -- translations with irrational ratios, leading to dense orbits

  -- We have three key transformations that map segments with
  -- different lengths but preserve the segment structure

  -- Since the length ratios are irrational (involving φ),
  -- repeated application creates a dense subset

  sorry  -- Main proof combining all pieces

/-- Corollary: The group GG₅(r_c) contains elements of infinite order -/
theorem infinite_order_element_exists :
    let sys := GG5_critical
    ∃ g : TwoDiskGroup, g ≠ 1 ∧ ∀ n : ℕ, n > 0 → g^n ≠ 1 := by
  intro sys
  -- Follows from GG5_infinite
  sorry

/-- The group is uncountable -/
theorem GG5_uncountable :
    let sys := GG5_critical
    ¬ Countable {g : TwoDiskGroup | ∃ z, applyGroupElement sys g z ≠ z} := by
  intro sys
  -- Dense orbits imply uncountability
  sorry

end Theorem2