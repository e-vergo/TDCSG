import TDCSG.TwoDisk.GoldenRatio

/-!
# GG₅ Specific Geometry

This file contains the geometric setup specific to GG₅ at the critical radius,
including the key points E, F, G and their properties.

## Main definitions

* `r_c`: The critical radius √(3 + φ)
* `E`, `F`, `G`: Key points for the Theorem 2 proof
* Geometric constraints and relationships

## Key results

* |E + 1| = r_c
* E, F, G are collinear on the line segment E'E
* |E - E'| / |F - F'| = φ
-/

open Complex Real
open scoped goldenRatio

namespace TwoDiskSystem

/-- The critical radius for GG₅: r_c = √(3 + φ) -/
noncomputable def r_c : ℝ := Real.sqrt (3 + φ)

/-- The key point E = ζ₅ - ζ₅² -/
noncomputable def E : ℂ := ζ₅ - ζ₅ ^ 2

/-- The key point E' = -E (by symmetry) -/
noncomputable def E' : ℂ := -E

/-- The key point F = 1 - ζ₅ + ζ₅² - ζ₅³ -/
noncomputable def F : ℂ := 1 - ζ₅ + ζ₅ ^ 2 - ζ₅ ^ 3

/-- The key point F' = -F -/
noncomputable def F' : ℂ := -F

/-- The key point G = 2F - E -/
noncomputable def G : ℂ := 2 * F - E

/-- The key point G' = -G -/
noncomputable def G' : ℂ := -G

/-- The geometric constraint: |E + 1| = r_c -/
theorem E_constraint : ‖E + 1‖ = r_c := by
  sorry

/-- F lies on the line segment from E' to E. -/
theorem F_on_segment_E'E :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F = E' + t • (E - E') := by
  sorry

/-- G lies on the line segment from E' to E. -/
theorem G_on_segment_E'E :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ G = E' + t • (E - E') := by
  sorry

/-- The ordering on the line: E', F', G, F, G', E (or similar). -/
theorem ordering_on_line :
    ∃ t_F t_G : ℝ, 0 < t_F ∧ t_F < t_G ∧ t_G < 1 ∧
      F = E' + t_F • (E - E') ∧
      G = E' + t_G • (E - E') := by
  sorry

/-- Key ratio: |E - E'| / |F - F'| = φ -/
theorem distance_ratio_phi :
    ‖E - E'‖ / ‖F - F'‖ = φ := by
  sorry

/-- The distance |F - F'|. -/
theorem distance_F_F' :
    ∃ d : ℝ, ‖F - F'‖ = d := by
  sorry

/-- The distance |E - G|. -/
theorem distance_E_G :
    ∃ d : ℝ, ‖E - G‖ = d := by
  sorry

/-- The two translation distances are not rationally related to the total length. -/
theorem translations_irrational_ratio :
    Irrational (‖E - E'‖ / ‖F - F'‖) := by
  sorry

end TwoDiskSystem
