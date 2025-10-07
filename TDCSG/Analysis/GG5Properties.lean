import TDCSG.Theory.Pentagon
import TDCSG.Tools.ComplexNormSimple

/-!
# GG₅ Specific Properties

This file analyzes specific properties of GG₅ at the critical radius.
New file created as part of Layer 4 (Analysis) to consolidate GG₅-specific analysis.

## Main theorems

* Geometric properties at critical radius
* Relationships between key points
-/

open Complex Real TwoDiskSystem ComplexNormTools
open scoped goldenRatio

namespace GG5Properties

/-- The critical GG₅ system -/
def GG5_critical : TwoDiskSystem :=
  { n₁ := 5
    n₂ := 5
    r₁ := r_c
    r₂ := r_c
    n₁_pos := by norm_num
    n₂_pos := by norm_num
    r₁_pos := r_c_pos
    r₂_pos := r_c_pos }

/-- At critical radius, the disks overlap with specific geometry -/
theorem critical_overlap :
    GG5_critical.diskIntersection.Nonempty := by
  use 0
  unfold diskIntersection leftDisk rightDisk
  simp [Metric.mem_closedBall, leftCenter, rightCenter]
  constructor
  · calc ‖(0 : ℂ) - (-1)‖ = ‖(1 : ℂ)‖ := by ring_nf
      _ = 1 := norm_one
      _ < r_c := by
        unfold r_c
        have : 1 < Real.sqrt (3 + goldenRatio) := by
          rw [one_lt_sqrt (by linarith [goldenRatio_pos] : 0 ≤ 3 + goldenRatio)]
          linarith [one_lt_goldenRatio]
        linarith
  · calc ‖(0 : ℂ) - 1‖ = ‖(-1 : ℂ)‖ := by ring_nf
      _ = 1 := by simp
      _ < r_c := by
        unfold r_c
        have : 1 < Real.sqrt (3 + goldenRatio) := by
          rw [one_lt_sqrt (by linarith [goldenRatio_pos] : 0 ≤ 3 + goldenRatio)]
          linarith [one_lt_goldenRatio]
        linarith

/-- The point E lies on the boundary of the left disk -/
theorem E_on_left_boundary :
    E ∈ Metric.sphere leftCenter r_c := by
  unfold E leftCenter
  simp [Metric.mem_sphere]
  exact E_constraint

/-- The symmetry relationship between points -/
theorem symmetry_relations :
    E' = -E ∧ F' = -F ∧ G' = -G := by
  exact ⟨E'_eq_neg_E, F'_eq_neg_F, G'_eq_neg_G⟩

/-- G is expressible in terms of E and F -/
theorem G_from_E_F : G = 2 * F - E := G_def

/-- The collinearity of E', F, G, E -/
theorem collinear_E_F_G :
    ∃ (a b : ℝ), 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ a < b ∧
    F = E' + a • (E - E') ∧
    G = E' + b • (E - E') := by
  obtain ⟨t_F, t_G, h1, h2, h3, h4, h5⟩ := ordering_on_line
  exact ⟨t_F, t_G, h1, h2, h3, h4, h5⟩

/-- The golden ratio appears in distance ratios -/
theorem golden_ratio_in_geometry :
    ‖E - E'‖ / ‖F - F'‖ = goldenRatio := distance_ratio_phi

end GG5Properties