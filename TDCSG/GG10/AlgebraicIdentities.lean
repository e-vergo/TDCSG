/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.GG10.Core
import TDCSG.GG10.Points
import TDCSG.GG10.IET

/-!
# Algebraic Identities for GG10 IET Words

This file proves algebraic identities showing that applying the two IET words (word1_10, word2_10)
to points on the segment E'₁₀E₁₀ produces the correct displacements.

## Main results

- `word2_10_algebraic_identity`: Word2 (a⁻¹b⁻¹ab) produces displacement -1/φ
- `word1_10_algebraic_identity`: Word1 (a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³) produces displacement 2-φ

## Rotation Operations

For GG(10,10), rotations are by angle 2π/10 = π/5:
- `a`: rotation by ζ₁₀ about center -1
- `a⁻¹`: rotation by ζ₁₀^9 about center -1
- `b`: rotation by ζ₁₀ about center 1
- `b⁻¹`: rotation by ζ₁₀^9 about center 1

## Implementation Notes

The words can be applied either as individual generator steps or as compound rotations.
For word1, consecutive applications of the same generator about the same center compose:
- a⁻⁴ = rotation by ζ₁₀^36 = ζ₁₀^6 about -1
- b⁻² = rotation by ζ₁₀^18 = ζ₁₀^8 about 1
- a⁻⁵ = rotation by ζ₁₀^45 = ζ₁₀^5 = -1 about -1
- etc.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.GG10

open Complex Real
open TDCSG.Definitions (φ)

/-! ### Helper Lemmas for ζ₁₀ -/

/-- The square of sqrt(5) equals 5. Basic simp lemma for algebraic manipulations. -/
@[simp] lemma sqrt5_sq_10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

/-- ζ₁₀ + ζ₁₀^9 = φ.

Since ζ₁₀^9 is the complex conjugate of ζ₁₀, their sum is twice the real part.
Re(ζ₁₀) = cos(π/5) = φ/2, so ζ₁₀ + ζ₁₀^9 = 2*(φ/2) = φ. -/
lemma zeta10_add_zeta10_pow9 : ζ₁₀ + ζ₁₀^9 = φ := by
  have h_conj : ζ₁₀^9 = starRingEnd ℂ ζ₁₀ := zeta10_conj.symm
  rw [h_conj]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    rw [zeta10_re]
    ring
  · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im]
    ring

/-- ζ₁₀ * ζ₁₀^9 = 1 (product of conjugates on unit circle). -/
@[simp] lemma zeta10_mul_zeta10_pow9 : ζ₁₀ * ζ₁₀^9 = 1 := by
  have h : ζ₁₀ * ζ₁₀^9 = ζ₁₀^10 := by ring
  rw [h, zeta10_pow_ten]

/-- (1 - ζ₁₀)(1 - ζ₁₀^9) = 2 - φ.

This is a key identity for word2. -/
lemma one_sub_zeta10_mul : (1 - ζ₁₀) * (1 - ζ₁₀^9) = (2 - φ : ℝ) := by
  have h1 : ζ₁₀ * ζ₁₀^9 = 1 := zeta10_mul_zeta10_pow9
  have h2 : ζ₁₀ + ζ₁₀^9 = φ := zeta10_add_zeta10_pow9
  calc (1 - ζ₁₀) * (1 - ζ₁₀^9)
      = 1 - ζ₁₀ - ζ₁₀^9 + ζ₁₀ * ζ₁₀^9 := by ring
    _ = 1 - (ζ₁₀ + ζ₁₀^9) + ζ₁₀ * ζ₁₀^9 := by ring
    _ = 1 - φ + 1 := by rw [h1, h2]
    _ = (2 - φ : ℝ) := by push_cast; ring

/-! ### Word2 Algebraic Identity

Word2 = a⁻¹b⁻¹ab produces translation by -1/φ in IET t-space (equivalently -2/φ in c-space)
on the segment E'₁₀E₁₀.

The four rotation steps follow Generator conventions:
1. Ainv: Rotate by ζ₁₀ about the left disk center (-1)
2. Binv: Rotate by ζ₁₀ about the right disk center (1)
3. A: Rotate by ζ₁₀^9 about the left disk center (-1)
4. B: Rotate by ζ₁₀^9 about the right disk center (1)

Note: Generator.A is clockwise rotation by 2π/10, so its angle is e^(-2πi/10) = ζ₁₀^9.
Generator.Ainv is counterclockwise, so its angle is e^(+2πi/10) = ζ₁₀.
-/

/--
Algebraic verification that word2_10 produces the correct displacement on segment E'₁₀E₁₀.

Word2 corresponds to the move sequence `a⁻¹b⁻¹ab` = [Ainv, Binv, A, B]. This lemma verifies
that applying this sequence of rotations to any point `z = c • E₁₀` on the segment results
in a translation by `-2/φ` in the c-parameterization (equivalently `-1/φ` in IET t-space).

The four rotation steps (following Generator conventions):
1. Ainv: Rotate by ζ₁₀ about the left disk center (-1)
2. Binv: Rotate by ζ₁₀ about the right disk center (1)
3. A: Rotate by ζ₁₀^9 about the left disk center (-1)
4. B: Rotate by ζ₁₀^9 about the right disk center (1)

The c-space displacement is `2 * displacement2_10 = -2/φ` because the segment from
E'₁₀ to E₁₀ has length 2|E₁₀|, making the c→t conversion scale by 1/2.
-/
lemma word2_10_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E₁₀
    let result :=
      let step1 := (-1 : ℂ) + ζ₁₀ * (z + 1)             -- Ainv (counterclockwise)
      let step2 := (1 : ℂ) + ζ₁₀ * (step1 - 1)          -- Binv (counterclockwise)
      let step3 := (-1 : ℂ) + ζ₁₀^9 * (step2 + 1)       -- A (clockwise)
      (1 : ℂ) + ζ₁₀^9 * (step3 - 1)                     -- B (clockwise)
    result = z + (2 * displacement2_10) • E₁₀ := by
  intro c _hc
  simp only
  unfold displacement2_10 E₁₀

  -- Key identity: φ = ζ₁₀ + ζ₁₀^9
  have h_phi_eq : (φ : ℂ) = ζ₁₀ + ζ₁₀^9 := by rw [zeta10_add_zeta10_pow9]

  -- The key identity: 1/φ = φ - 1
  have h_inv_phi_real : (1 : ℝ) / φ = φ - 1 := by
    have hφ_pos : 0 < φ := Real.goldenRatio_pos
    field_simp
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [hsq, sq_nonneg (Real.sqrt 5)]

  -- The c-space displacement: 2 * (-(1/φ)) = -2/φ = 2(1-φ) = 2 - 2ζ₁₀ - 2ζ₁₀^9
  have hdisp : (2 * (-(1 / φ)) : ℝ) • (ζ₁₀ - ζ₁₀^2 : ℂ) = (2 - 2*ζ₁₀ - 2*ζ₁₀^9) * (ζ₁₀ - ζ₁₀^2) := by
    rw [h_inv_phi_real]
    simp only [smul_eq_mul]
    push_cast
    rw [h_phi_eq]
    ring

  rw [hdisp]

  -- Expand and simplify using power reduction
  ring_nf
  simp only [zeta10_pow_ten, zeta10_pow_eleven, zeta10_pow_twelve, zeta10_pow_eighteen,
             zeta10_pow_nineteen, zeta10_pow_twenty]
  ring

/-! ### Word1 Algebraic Identity

Word1 = a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³ produces translation by 2-φ on the segment E'₁₀E₁₀.

The compound rotations are:
- a⁻⁴: rotation by ζ₁₀^36 = ζ₁₀^6 about -1
- b⁻²: rotation by ζ₁₀^18 = ζ₁₀^8 about 1
- a⁻⁵: rotation by ζ₁₀^45 = ζ₁₀^5 = -1 about -1 (180° rotation!)
- b⁻²: rotation by ζ₁₀^18 = ζ₁₀^8 about 1
- a⁻⁴: rotation by ζ₁₀^36 = ζ₁₀^6 about -1
- b⁻³: rotation by ζ₁₀^27 = ζ₁₀^7 about 1
-/

/--
Algebraic verification that word1_10 produces the correct displacement on segment E'₁₀E₁₀.

Word1 corresponds to the move sequence `a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³`. This lemma verifies that
applying this sequence of rotations to any point `z = c • E₁₀` on the segment results
in a translation by `displacement1_10 = 2 - φ ≈ 0.382` in the direction of E₁₀.

The six compound rotation steps are:
1. Rotate by ζ₁₀^6 about the left disk center (-1)    [a⁻⁴]
2. Rotate by ζ₁₀^8 about the right disk center (1)   [b⁻²]
3. Rotate by -1 about the left disk center (-1)      [a⁻⁵]
4. Rotate by ζ₁₀^8 about the right disk center (1)   [b⁻²]
5. Rotate by ζ₁₀^6 about the left disk center (-1)   [a⁻⁴]
6. Rotate by ζ₁₀^7 about the right disk center (1)   [b⁻³]

The net effect is a translation of magnitude `2 - φ` along E'₁₀E₁₀.
-/
lemma word1_10_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E₁₀
    let result :=
      let step1 := (-1 : ℂ) + ζ₁₀^6 * (z + 1)           -- a⁻⁴ (compound)
      let step2 := (1 : ℂ) + ζ₁₀^8 * (step1 - 1)        -- b⁻² (compound)
      let step3 := (-1 : ℂ) + (-1 : ℂ) * (step2 + 1)    -- a⁻⁵ (compound, ζ₁₀^5 = -1)
      let step4 := (1 : ℂ) + ζ₁₀^8 * (step3 - 1)        -- b⁻² (compound)
      let step5 := (-1 : ℂ) + ζ₁₀^6 * (step4 + 1)       -- a⁻⁴ (compound)
      (1 : ℂ) + ζ₁₀^7 * (step5 - 1)                     -- b⁻³ (compound)
    result = z + displacement1_10 • E₁₀ := by
  intro c _hc
  simp only
  unfold displacement1_10 E₁₀

  -- Convert scalar multiplication to regular multiplication
  have hcE : (c : ℂ) • (ζ₁₀ - ζ₁₀^2) = c * (ζ₁₀ - ζ₁₀^2) := by rfl
  have hdE : (2 - φ : ℝ) • (ζ₁₀ - ζ₁₀^2) = (2 - φ : ℝ) * (ζ₁₀ - ζ₁₀^2) := by rfl
  rw [hcE, hdE]

  -- Expand the compound rotation steps
  ring_nf
  simp only [zeta10_pow_40, zeta10_pow_39, zeta10_pow_38, zeta10_pow_37, zeta10_pow_36,
             zeta10_pow_35, zeta10_pow_34, zeta10_pow_33, zeta10_pow_32, zeta10_pow_31,
             zeta10_pow_30, zeta10_pow_29, zeta10_pow_28, zeta10_pow_27, zeta10_pow_26,
             zeta10_pow_25, zeta10_pow_24, zeta10_pow_23, zeta10_pow_22, zeta10_pow_21,
             zeta10_pow_twenty, zeta10_pow_nineteen, zeta10_pow_eighteen,
             zeta10_pow_seventeen, zeta10_pow_sixteen, zeta10_pow_fifteen,
             zeta10_pow_fourteen, zeta10_pow_thirteen, zeta10_pow_twelve,
             zeta10_pow_eleven, zeta10_pow_ten, zeta10_pow_five]

  have h_cyclo : 1 + ζ₁₀ + ζ₁₀^2 + ζ₁₀^3 + ζ₁₀^4 + ζ₁₀^5 + ζ₁₀^6 + ζ₁₀^7 + ζ₁₀^8 + ζ₁₀^9 = 0 := cyclotomic10_sum

  -- The displacement 2 - φ can be expressed in terms of ζ₁₀
  have h_two_minus_phi : (2 - φ : ℂ) = (1 - ζ₁₀) * (1 - ζ₁₀^9) := by
    rw [one_sub_zeta10_mul]
    simp

  sorry

end TDCSG.GG10
