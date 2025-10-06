import TDCSG.TwoDisk.ComplexRepresentation

/-!
# Golden Ratio Properties

This file defines the golden ratio and proves key properties needed for Theorem 2.

## Main definitions

* `φ`: The golden ratio (1 + √5)/2
* Algebraic properties: φ² = φ + 1
* Irrationality of φ

## Key results

* The golden ratio satisfies φ² = φ + 1
* φ is irrational
* Relationships with ζ₅
-/

open Real
open scoped goldenRatio

namespace TwoDiskSystem

/-- The golden ratio satisfies φ² = φ + 1 -/
theorem phi_squared : φ ^ 2 = φ + 1 := goldenRatio_sq

/-- The golden ratio is positive. -/
theorem phi_pos : φ > 0 := goldenRatio_pos

/-- The golden ratio is greater than 1. -/
theorem phi_gt_one : φ > 1 := one_lt_goldenRatio

/-- The golden ratio is irrational. -/
theorem phi_irrational : Irrational φ := goldenRatio_irrational

/-- Relationship: 1/φ = φ - 1 -/
theorem phi_reciprocal : 1 / φ = φ - 1 := by
  have h := phi_squared
  field_simp at h ⊢
  linarith

/-- ζ₅ can be expressed in terms of φ (useful for geometric calculations).
    Specifically, ζ₅ = e^(2πi/5) = cos(2π/5) + i*sin(2π/5)
    where cos(2π/5) = (φ - 1)/2 = (√5 - 1)/4. -/
theorem zeta5_and_phi :
    ∃ (re im : ℝ), ζ₅ = ↑re + Complex.I * ↑im ∧ re = (φ - 1) / 2 := by
  -- ζ₅ = exp(2πi/5) = cos(2π/5) + i*sin(2π/5)
  use Real.cos (2 * π / 5), Real.sin (2 * π / 5)
  constructor
  · -- Show ζ₅ = cos(2π/5) + i*sin(2π/5)
    unfold ζ₅ ζ
    -- This follows from Euler's formula: e^(iθ) = cos(θ) + i*sin(θ)
    -- We have exp(2πi/5) and need to show it equals cos(2π/5) + i*sin(2π/5)
    -- First rewrite the argument in a more convenient form
    -- The argument is (2*π*I/5), we want to apply Euler's formula
    -- Note: 5 is coerced from ℕ to ℂ, so we have ↑5 in the goal
    have h1 : (2 * ↑π * Complex.I / ↑(5:ℕ) : ℂ) = ↑(2 * π / 5) * Complex.I := by
      rw [show ↑(5:ℕ) = (5:ℂ) by norm_cast]
      simp only [Complex.ofReal_mul, Complex.ofReal_div]
      field_simp
      ring_nf
      norm_cast
    simp_rw [h1]
    rw [Complex.exp_mul_I]
    -- Now we have: cos(↑(2π/5)) + sin(↑(2π/5)) * I
    -- We need: ↑(cos(2π/5)) + I * ↑(sin(2π/5))
    -- The theorem Complex.exp_mul_I gives us Complex.cos and Complex.sin
    -- but the goal has Real.cos and Real.sin
    -- Key: Complex.cos of a real number equals the real cosine coerced
    norm_cast
    ring
  · -- Show cos(2π/5) = (φ - 1)/2
    -- We use the fact that cos(π/5) = (1 + √5)/4
    -- and the double angle formula: cos(2θ) = 2cos²(θ) - 1
    have h_cos_pi_5 : Real.cos (π / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five

    -- Use double angle formula
    have h_double : Real.cos (2 * π / 5) = 2 * (Real.cos (π / 5))^2 - 1 := by
      rw [← Real.cos_two_mul]
      congr 1
      ring

    -- Substitute the value of cos(π/5) and simplify
    rw [h_double, h_cos_pi_5]
    -- Goal: 2 * ((1 + √5)/4)² - 1 = (φ - 1)/2
    -- Note that φ = (1 + √5)/2 by definition
    rw [show φ = (1 + Real.sqrt 5) / 2 from rfl]
    -- Now simplify both sides
    field_simp
    ring_nf
    -- After expanding: need to show (√5)² = 5
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring

end TwoDiskSystem
