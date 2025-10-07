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
  -- Strategy: compute ‖1 + ζ₅ - ζ₅²‖² and show it equals 3 + φ

  -- This is a detailed algebraic calculation
  -- We'll use the fact that for roots of unity, conjugation = inversion
  sorry

/-- F lies on the line segment from E' to E. -/
theorem F_on_segment_E'E :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F = E' + t • (E - E') := by
  -- Strategy: We'll use the fact that E - E' = 2E, and express F in terms of E
  -- From the sum of fifth roots: 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0

  -- First, let's establish that E - E' = 2E
  have h_diff : E - E' = 2 • E := by
    unfold E E'
    simp [two_smul]
    ring

  -- Now we need to show F can be written as E' + t•(2E) for some t ∈ (0,1)
  -- F = 1 - ζ₅ + ζ₅² - ζ₅³
  -- E' = -ζ₅ + ζ₅²
  -- E = ζ₅ - ζ₅²

  -- Let's try to find t such that F = E' + 2t•E
  -- F = (-ζ₅ + ζ₅²) + 2t(ζ₅ - ζ₅²)
  -- F = -ζ₅ + ζ₅² + 2tζ₅ - 2tζ₅²
  -- F = (2t - 1)ζ₅ + (1 - 2t)ζ₅²

  -- But F = 1 - ζ₅ + ζ₅² - ζ₅³
  -- We need to use sum_zeta5_powers: ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ + 1 = 0
  -- to rewrite 1 in terms of ζ₅ powers

  -- This requires detailed algebraic manipulation with the constraint
  -- For now, we note this is a computational problem
  sorry  -- Requires: (1) Expressing 1 and ζ₅³ using sum_zeta5_powers
         --          (2) Collecting coefficients to solve for t
         --          (3) Verifying t ∈ (0,1) numerically or via properties of φ

/-- G lies on the line segment from E' to E. -/
theorem G_on_segment_E'E :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ G = E' + t • (E - E') := by
  -- Strategy: Use G = 2F - E and the fact that F is on the segment
  -- If F = E' + t_F • (E - E'), then we can express G similarly

  -- From F_on_segment_E'E, we know F = E' + t_F • (E - E') for some t_F ∈ (0,1)
  -- G = 2F - E
  -- We showed earlier that E - E' = 2E, so E = E' + (1/2)•(E - E') wouldn't work...
  -- Actually, E - E' = 2E means E' = E - 2E = -E, which is correct by definition

  -- Let's work algebraically:
  -- G = 2F - E
  -- If F = E' + t_F•(E - E'), then:
  -- G = 2(E' + t_F•(E - E')) - E
  -- G = 2E' + 2t_F•(E - E') - E

  -- We need to express -E in terms of E' and E
  -- E' = -E, so E = -E'
  -- E - E' = E - (-E) = 2E (confirmed earlier)
  -- So E' = -E and E = -E'

  -- Therefore: G = 2E' + 2t_F•(E - E') + E'  (since -E = E')
  -- G = 3E' + 2t_F•(E - E')

  -- Hmm, this doesn't have the right form. Let me reconsider...
  -- Actually, if all points are collinear, then G being between E' and E
  -- is a consequence of the specific values, which requires computation.

  sorry  -- Requires: (1) Using F_on_segment_E'E to get t_F
         --          (2) Computing t_G from G = 2F - E algebraically
         --          (3) Showing 0 < t_G < 1 from properties of t_F and geometry

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
