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
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
    simp only [mul_comm I, re_ofReal_mul_im, im_ofReal_mul_im, ofReal_div, ofReal_mul]
    norm_num
    ring_nf
    rw [mul_comm (Real.sin _), mul_comm (Real.cos _)]
    simp only [Complex.I_re, Complex.I_im]
    norm_num
    ext <;> simp [Real.sin, Real.cos]
  · -- Show cos(2π/5) = (φ - 1)/2
    -- This is a classical result about regular pentagons
    -- cos(2π/5) = (√5 - 1)/4 = (φ - 1)/2
    sorry  -- This requires the specific value of cos(2π/5) in terms of φ

end TwoDiskSystem
