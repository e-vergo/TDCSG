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

/-- The critical radius is positive -/
theorem r_c_pos : r_c > 0 := by
  unfold r_c
  apply Real.sqrt_pos.mpr
  have h := phi_gt_one
  linarith

/-- The key point E = ζ₅ - ζ₅² -/
noncomputable def E : ℂ := ζ₅ - ζ₅ ^ 2

/-- The key point E' = -E (by symmetry) -/
noncomputable def E' : ℂ := -E

/-- E' equals -E by definition -/
theorem E'_eq_neg_E : E' = -E := rfl

/-- The key point F = 1 - ζ₅ + ζ₅² - ζ₅³ -/
noncomputable def F : ℂ := 1 - ζ₅ + ζ₅ ^ 2 - ζ₅ ^ 3

/-- The key point F' = -F -/
noncomputable def F' : ℂ := -F

/-- F' equals -F by definition -/
theorem F'_eq_neg_F : F' = -F := rfl

/-- The key point G = 2F - E -/
noncomputable def G : ℂ := 2 * F - E

/-- G equals 2F - E by definition -/
theorem G_def : G = 2 * F - E := rfl

/-- The key point G' = -G -/
noncomputable def G' : ℂ := -G

/-- G' equals -G by definition -/
theorem G'_eq_neg_G : G' = -G := rfl

/-- The geometric constraint: |E + 1| = r_c -/
theorem E_constraint : ‖E + 1‖ = r_c := by
  unfold E r_c
  -- E = ζ₅ - ζ₅², so E + 1 = 1 + ζ₅ - ζ₅²
  -- We need to show ‖1 + ζ₅ - ζ₅²‖ = √(3 + φ)
  -- This requires expanding using properties of ζ₅ and computing the norm
  -- The calculation involves using that ζ₅ = e^(2πi/5) = cos(2π/5) + i*sin(2π/5)
  -- and the specific values of cos(2π/5) and sin(2π/5) in terms of φ
  sorry  -- Requires detailed calculation with fifth roots of unity

/-- F lies on the line segment from E' to E. -/
theorem F_on_segment_E'E :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F = E' + t • (E - E') := by
  -- This requires computing the specific value of t
  -- F = 1 - ζ₅ + ζ₅² - ζ₅³, E = ζ₅ - ζ₅², E' = -E
  -- The proof would involve showing F is a convex combination of E' and E
  sorry

/-- G lies on the line segment from E' to E. -/
theorem G_on_segment_E'E :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ G = E' + t • (E - E') := by
  -- G = 2*F - E by definition
  -- This requires showing that G lies between E' and E
  -- Would need specific calculations with ζ₅
  sorry

/-- The ordering on the line: E', F', G, F, G', E (or similar). -/
theorem ordering_on_line :
    ∃ t_F t_G : ℝ, 0 < t_F ∧ t_F < t_G ∧ t_G < 1 ∧
      F = E' + t_F • (E - E') ∧
      G = E' + t_G • (E - E') := by
  -- This follows from F_on_segment_E'E and G_on_segment_E'E
  -- with the additional ordering constraint t_F < t_G
  sorry  -- Requires computation with ζ₅ to determine specific values

/-- Key ratio: |E - E'| / |F - F'| = φ -/
theorem distance_ratio_phi :
    ‖E - E'‖ / ‖F - F'‖ = φ := by
  -- E' = -E and F' = -F, so:
  -- E - E' = E - (-E) = 2E
  -- F - F' = F - (-F) = 2F
  rw [E'_eq_neg_E, F'_eq_neg_F]
  simp only [sub_neg_eq_add]
  -- Now we have ‖E + E‖ / ‖F + F‖
  -- which equals ‖2 • E‖ / ‖2 • F‖
  conv_lhs =>
    arg 1
    rw [← two_smul ℂ E]
  conv_lhs =>
    arg 2
    rw [← two_smul ℂ F]
  rw [norm_smul, norm_smul]
  -- ‖2‖ * ‖E‖ / (‖2‖ * ‖F‖) = φ
  have h2 : (‖(2 : ℂ)‖ : ℝ) ≠ 0 := by
    norm_num
  field_simp [h2]
  ring_nf
  -- Now we have ‖E‖ = φ * ‖F‖
  -- The actual calculation requires expanding E and F in terms of ζ₅
  sorry  -- Requires detailed calculation

/-- The distance |F - F'|. -/
theorem distance_F_F' :
    ∃ d : ℝ, ‖F - F'‖ = d := by
  use ‖F - F'‖

/-- The distance |E - G|. -/
theorem distance_E_G :
    ∃ d : ℝ, ‖E - G‖ = d := by
  use ‖E - G‖

/-- The two translation distances are not rationally related to the total length. -/
theorem translations_irrational_ratio :
    Irrational (‖E - E'‖ / ‖F - F'‖) := by
  rw [distance_ratio_phi]
  exact phi_irrational

end TwoDiskSystem
