import TDCSG.TwoDisk.Theorem1

/-!
# Complex Plane Representation

This file sets up the complex plane representation and roots of unity
needed for Theorem 2.

## Main definitions

* `ζ n`: The primitive n-th root of unity e^(2πi/n)
* Properties of ζ₅ (fifth roots of unity)
* Rotation as complex multiplication

## Key lemmas

* Properties of roots of unity
* Relationship between rotations and complex multiplication
-/

open Complex Real

namespace TwoDiskSystem

/-- The primitive n-th root of unity: ζₙ = e^(2πi/n) -/
noncomputable def ζ (n : ℕ) : ℂ := exp (2 * π * I / n)

/-- ζ₅ is specifically the fifth root of unity. -/
noncomputable def ζ₅ : ℂ := ζ 5

/-- ζₙ^n = 1 -/
theorem zeta_pow_n (n : ℕ) (hn : n > 0) : (ζ n) ^ n = 1 := by
  unfold ζ
  rw [← Complex.exp_nat_mul, mul_div_cancel₀]
  · exact exp_two_pi_mul_I
  · exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)

/-- |ζₙ| = 1 -/
theorem zeta_abs (n : ℕ) (_hn : n > 0) : ‖ζ n‖ = 1 := by
  unfold ζ
  rw [norm_exp]
  simp only [mul_comm, div_re]
  norm_num

/-- ζₙ⁻¹ = ζₙ̄ (complex conjugate) -/
theorem zeta_inv (n : ℕ) (hn : n > 0) : (ζ n)⁻¹ = starRingEnd ℂ (ζ n) := by
  exact inv_eq_conj (zeta_abs n hn)

/-- Express rotation by angle θ around center c as complex multiplication. -/
theorem rotation_as_multiplication (θ : ℝ) (c z : ℂ) :
    c + exp (I * (θ : ℂ)) * (z - c) = c + (↑(Real.cos θ) + I * ↑(Real.sin θ)) * (z - c) := by
  congr 1
  rw [mul_comm I, exp_mul_I]
  rw [← ofReal_cos, ← ofReal_sin]
  ring

/-- Left rotation can be expressed using ζₙ₁. -/
theorem leftRotation_as_zeta (sys : TwoDiskSystem) (z : ℂ) (hz : z ∈ sys.leftDisk) :
    sys.leftRotation z = leftCenter + (ζ sys.n₁)⁻¹ * (z - leftCenter) := by
  unfold leftRotation
  rw [if_pos hz]
  congr 1
  unfold ζ leftAngle
  rw [show (I * ↑(-2 * Real.pi / ↑sys.n₁)) = -(2 * ↑Real.pi * I / ↑sys.n₁) by
    simp only [ofReal_neg, ofReal_div, ofReal_mul, ofReal_natCast]
    norm_num
    field_simp]
  rw [Complex.exp_neg]

/-- Right rotation can be expressed using ζₙ₂. -/
theorem rightRotation_as_zeta (sys : TwoDiskSystem) (z : ℂ) (hz : z ∈ sys.rightDisk) :
    sys.rightRotation z = rightCenter + (ζ sys.n₂)⁻¹ * (z - rightCenter) := by
  unfold rightRotation
  rw [if_pos hz]
  congr 1
  unfold ζ rightAngle
  rw [show (I * ↑(-2 * Real.pi / ↑sys.n₂)) = -(2 * ↑Real.pi * I / ↑sys.n₂) by
    simp only [ofReal_neg, ofReal_div, ofReal_mul, ofReal_natCast]
    norm_num
    field_simp]
  rw [Complex.exp_neg]

/-- ζₙ is nonzero -/
theorem zeta_ne_zero (n : ℕ) (hn : n > 0) : ζ n ≠ 0 := by
  intro h
  have := zeta_abs n hn
  rw [h, norm_zero] at this
  norm_num at this

/-- ζ₅⁵ = 1 (special case of zeta_pow_n) -/
theorem zeta5_pow_5 : ζ₅ ^ 5 = 1 := by
  exact zeta_pow_n 5 (by norm_num : 5 > 0)

/-- ζ₅⁴ = ζ₅⁻¹ -/
theorem zeta5_pow_4 : ζ₅ ^ 4 = ζ₅⁻¹ := by
  have h := zeta5_pow_5
  -- ζ₅⁵ = ζ₅ * ζ₅⁴ = 1, so ζ₅⁴ = ζ₅⁻¹
  have hz : ζ₅ ≠ 0 := zeta_ne_zero 5 (by norm_num : 5 > 0)
  rw [pow_succ, mul_comm] at h
  field_simp [hz] at h ⊢
  exact h

/-- ζ₅ is a primitive fifth root of unity -/
theorem zeta5_is_primitive : IsPrimitiveRoot ζ₅ 5 := by
  unfold ζ₅ ζ
  exact Complex.isPrimitiveRoot_exp 5 (by norm_num : 5 ≠ 0)

/-- Sum of all fifth roots of unity equals 0 -/
theorem sum_zeta5_powers : ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 + 1 = 0 := by
  have h := zeta5_is_primitive.geom_sum_eq_zero (by norm_num : 1 < 5)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero] at h
  ring_nf at h
  -- h : 1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0
  -- Need to show: ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 + 1 = 0
  rw [← h]
  abel

end TwoDiskSystem
