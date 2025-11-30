/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points
import TDCSG.Definitions.WordCorrespondence
import TDCSG.Proofs.Zeta5
import TDCSG.Proofs.IET

/-!
# Algebraic Identities for Word Actions

This file contains the core algebraic identities proving that each word
(word1, word2, word3) acts as a translation on E-multiples.

## Main Results

- `word1_algebraic_identity`: word1 = AABAB translates by 2*displacement0*E
- `word2_algebraic_identity`: word2 = A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ translates by 2*displacement1*E
- `word3_algebraic_identity`: word3 = A⁻¹B⁻¹A⁻¹BAB translates by 2*displacement2*E
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions CompoundSymmetry.GG5

/-- Key algebraic identity for word1 = AABAB (a²bab) acting on E-multiples.

For any point of the form c*E on segment E'E, applying word1 translates it by 2*displacement0*E.
This is the core algebraic fact verified by computing through the zeta5 rotations.

Forward rotation formulas (clockwise convention):
- A: z ↦ -1 + ζ₅⁴ * (z + 1)  (rotation by -2π/5 about -1)
- B: z ↦ 1 + ζ₅⁴ * (z - 1)   (rotation by -2π/5 about 1)

With clockwise convention and E = ζ₅⁴ - ζ₅³:
- F = 1 - ζ₅⁴ + ζ₅³ - ζ₅² = (1/φ) * E
- The word produces translation by 2*F = (2/φ)*E = 2*displacement0*E

Word1 = [A, A, B, A, B] applied left to right. -/
lemma word1_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E
    let result := -- A A B A B applied in complex form (forward rotations with ζ₅⁴)
      let step1 := (-1 : ℂ) + ζ₅^4 * (z + 1)         -- A
      let step2 := (-1 : ℂ) + ζ₅^4 * (step1 + 1)     -- A
      let step3 := (1 : ℂ) + ζ₅^4 * (step2 - 1)      -- B
      let step4 := (-1 : ℂ) + ζ₅^4 * (step3 + 1)     -- A
      (1 : ℂ) + ζ₅^4 * (step4 - 1)                   -- B
    result = z + (2 * displacement0) • E := by
  intro c _hc
  simp only
  -- Key power reduction lemmas
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
  have h7 : ζ₅^7 = ζ₅^2 := zeta5_pow_seven
  have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
  have h11 : ζ₅^11 = ζ₅ := zeta5_pow_eleven
  have h12 : ζ₅^12 = ζ₅^2 := zeta5_pow_twelve
  have h16 : ζ₅^16 = ζ₅ := zeta5_pow_sixteen
  have h17 : ζ₅^17 = ζ₅^2 := zeta5_pow_seventeen
  have h18 : ζ₅^18 = ζ₅^3 := by have := zeta5_pow_reduce 18; norm_num at this; exact this
  have h19 : ζ₅^19 = ζ₅^4 := by have := zeta5_pow_reduce 19; norm_num at this; exact this
  have h20 : ζ₅^20 = (1 : ℂ) := by have := zeta5_pow_reduce 20; norm_num at this; exact this
  have h23 : ζ₅^23 = ζ₅^3 := by have := zeta5_pow_reduce 23; norm_num at this; exact this
  have h24 : ζ₅^24 = ζ₅^4 := by have := zeta5_pow_reduce 24; norm_num at this; exact this
  -- sqrt 5 squared equals 5
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- Key identity: F = (1/φ)*E where F = 1 - ζ₅⁴ + ζ₅³ - ζ₅² and E = ζ₅⁴ - ζ₅³
  -- First establish ζ₅ + ζ₅⁴ = (√5-1)/2 = 1/φ
  have h_sum1 : ζ₅ + ζ₅^4 = ((Real.sqrt 5 - 1) / 2 : ℝ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      rw [zeta5_re, zeta5_pow4_re]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im]
      rw [zeta5_im_eq_sin, zeta5_pow4_im_neg, zeta5_im_eq_sin]
      ring
  -- F = 1 - ζ₅⁴ + ζ₅³ - ζ₅² = (1/φ) * (ζ₅⁴ - ζ₅³)
  have h_F_eq : (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 = (1 / Real.goldenRatio : ℝ) * (ζ₅^4 - ζ₅^3) := by
    -- Factor: (1 - ζ₅⁴ + ζ₅³ - ζ₅²) = (ζ₅ + ζ₅⁴) * (ζ₅⁴ - ζ₅³)
    have h_factor : (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) = (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 := by
      calc (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3)
          = ζ₅^5 - ζ₅^4 + ζ₅^8 - ζ₅^7 := by ring
        _ = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 := by rw [h5, h8, h7]
    calc (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2
        = (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) := h_factor.symm
      _ = ((Real.sqrt 5 - 1) / 2 : ℝ) * (ζ₅^4 - ζ₅^3) := by rw [h_sum1]
      _ = (1 / Real.goldenRatio : ℝ) * (ζ₅^4 - ζ₅^3) := by
          congr 1
          simp only [Complex.ofReal_inj]
          unfold Real.goldenRatio
          have h_cross : (Real.sqrt 5 - 1) * (1 + Real.sqrt 5) = 4 := by
            calc (Real.sqrt 5 - 1) * (1 + Real.sqrt 5)
                = Real.sqrt 5 + Real.sqrt 5 ^ 2 - 1 - Real.sqrt 5 := by ring
              _ = Real.sqrt 5 + 5 - 1 - Real.sqrt 5 := by rw [hsqrt5_sq]
              _ = 4 := by ring
          field_simp
          linarith
  -- Now unfold and compute with E = ζ₅⁴ - ζ₅³
  unfold displacement0 length3 E
  -- Convert smul to mul for complex arithmetic
  have hcE : (c : ℂ) • (ζ₅^4 - ζ₅^3) = c * (ζ₅^4 - ζ₅^3) := by rfl
  have h2dE : (2 * (1 / Real.goldenRatio)) • (ζ₅^4 - ζ₅^3) =
              (2 * (1 / Real.goldenRatio) : ℝ) * (ζ₅^4 - ζ₅^3) := by rfl
  rw [hcE, h2dE]
  -- The expansion of word1 with E = ζ₅⁴ - ζ₅³ gives translation by 2*F
  have h_expand : (1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (↑c * (ζ₅^4 - ζ₅^3) + 1) + 1) - 1) + 1) - 1)
      = ↑c * (ζ₅^4 - ζ₅^3) + 2 * ((1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2) := by
    ring_nf
    -- After ring_nf, reduce high powers modulo 5
    simp only [h24, h23, h20, h12, h8]
    -- Use cyclotomic sum identity: 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0
    have h_zeta_sum : (1 : ℂ) + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0 := cyclotomic5_sum
    have h4_expand : ζ₅^4 = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by
      calc ζ₅^4 = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + (1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4) := by ring
        _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + 0 := by rw [h_zeta_sum]
        _ = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by ring
    rw [h4_expand]
    ring
  rw [h_expand, h_F_eq]
  push_cast
  ring

/-- Key algebraic identity for word2 = A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ acting on E-multiples.

For any point of the form c*E on segment E'E, applying word2 translates it by 2*displacement1*E.
Since displacement1 = displacement0 = 1/φ, this equals 2*(1/φ)*E.

Rotation formulas (clockwise convention: A⁻¹ = A⁴ uses ζ₅):
- A⁻¹: z ↦ -1 + ζ₅ * (z + 1)   (rotation by +2π/5 about -1, inverse of clockwise A)
- B⁻¹: z ↦ 1 + ζ₅ * (z - 1)    (rotation by +2π/5 about 1, inverse of clockwise B)

Word2 = [A⁻¹, B⁻¹, A⁻¹, B⁻¹, B⁻¹] applied left to right.
Encoded as: [Generator.Ainv, Generator.Binv, Generator.Ainv, Generator.Binv, Generator.Binv]

Intermediate steps for z₀ = c•E:
- z₁ = -1 + ζ₅(z₀ + 1)   -- After A⁻¹
- z₂ = 1 + ζ₅(z₁ - 1)    -- After B⁻¹
- z₃ = -1 + ζ₅(z₂ + 1)   -- After A⁻¹
- z₄ = 1 + ζ₅(z₃ - 1)    -- After B⁻¹
- z₅ = 1 + ζ₅(z₄ - 1)    -- After B⁻¹ (final)

The composition gives z₅ = z₀ + 2*(1/φ)*E = z₀ + 2*displacement1*E. -/
lemma word2_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E
    let result := -- A⁻¹ B⁻¹ A⁻¹ B⁻¹ B⁻¹ applied in complex form (ζ₅ for inverses)
      let step1 := (-1 : ℂ) + ζ₅ * (z + 1)         -- A⁻¹
      let step2 := (1 : ℂ) + ζ₅ * (step1 - 1)      -- B⁻¹
      let step3 := (-1 : ℂ) + ζ₅ * (step2 + 1)     -- A⁻¹
      let step4 := (1 : ℂ) + ζ₅ * (step3 - 1)      -- B⁻¹
      (1 : ℂ) + ζ₅ * (step4 - 1)                   -- B⁻¹
    result = z + (2 * displacement1) • E := by
  intro c _hc
  simp only
  -- Key power reduction lemmas
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
  have h7 : ζ₅^7 = ζ₅^2 := zeta5_pow_seven
  have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
  -- sqrt 5 squared equals 5
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- displacement1 = displacement0 = 1/φ
  have h_disp : displacement1 = 1 / Real.goldenRatio := by
    rw [displacement0_eq_displacement1.symm]
    unfold displacement0 length3
    ring
  -- The key identity: F = (1/φ)*E where F = 1 - ζ₅⁴ + ζ₅³ - ζ₅² and E = ζ₅⁴ - ζ₅³
  have h_sum1 : ζ₅ + ζ₅^4 = ((Real.sqrt 5 - 1) / 2 : ℝ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      rw [zeta5_re, zeta5_pow4_re]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im]
      rw [zeta5_im_eq_sin, zeta5_pow4_im_neg, zeta5_im_eq_sin]
      ring
  -- F = 1 - ζ₅⁴ + ζ₅³ - ζ₅² = (1/φ) * (ζ₅⁴ - ζ₅³) for clockwise E
  have h_F_eq : (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 = (1 / Real.goldenRatio : ℝ) * (ζ₅^4 - ζ₅^3) := by
    -- Factor: (1 - ζ₅⁴ + ζ₅³ - ζ₅²) = (ζ₅ + ζ₅⁴) * (ζ₅⁴ - ζ₅³)
    have h_factor : (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) = (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 := by
      calc (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3)
          = ζ₅^5 - ζ₅^4 + ζ₅^8 - ζ₅^7 := by ring
        _ = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 := by rw [h5, h8, h7]
    calc (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2
        = (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) := h_factor.symm
      _ = ((Real.sqrt 5 - 1) / 2 : ℝ) * (ζ₅^4 - ζ₅^3) := by rw [h_sum1]
      _ = (1 / Real.goldenRatio : ℝ) * (ζ₅^4 - ζ₅^3) := by
          congr 1
          simp only [Complex.ofReal_inj]
          unfold Real.goldenRatio
          have h_cross : (Real.sqrt 5 - 1) * (1 + Real.sqrt 5) = 4 := by
            calc (Real.sqrt 5 - 1) * (1 + Real.sqrt 5)
                = Real.sqrt 5 + Real.sqrt 5 ^ 2 - 1 - Real.sqrt 5 := by ring
              _ = Real.sqrt 5 + 5 - 1 - Real.sqrt 5 := by rw [hsqrt5_sq]
              _ = 4 := by ring
          field_simp
          linarith
  -- Now unfold and compute with E = ζ₅⁴ - ζ₅³
  unfold displacement1 length3 E
  -- Convert smul to mul for complex arithmetic
  have hcE : (c : ℂ) • (ζ₅^4 - ζ₅^3) = c * (ζ₅^4 - ζ₅^3) := by rfl
  have h2dE : (2 * (1 / Real.goldenRatio)) • (ζ₅^4 - ζ₅^3) =
              (2 * (1 / Real.goldenRatio) : ℝ) * (ζ₅^4 - ζ₅^3) := by rfl
  rw [hcE, h2dE]
  -- The expansion of word2 = A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ produces translation by 2*(1 - ζ₅⁴ + ζ₅³ - ζ₅²)
  -- With ζ₅ for all inverse rotations
  have h_expand : (1 : ℂ) + ζ₅ * ((1 : ℂ) + ζ₅ * ((-1 : ℂ) + ζ₅ * ((1 : ℂ) + ζ₅ * ((-1 : ℂ) + ζ₅ * (↑c * (ζ₅^4 - ζ₅^3) + 1) - 1) + 1) - 1) - 1)
      = ↑c * (ζ₅^4 - ζ₅^3) + 2 * ((1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2) := by
    ring_nf
    -- After ring_nf, reduce powers modulo 5
    have h9 : ζ₅^9 = ζ₅^4 := zeta5_pow_nine
    simp only [h9, h8, h5]
    -- Use cyclotomic sum identity: 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0
    have h_zeta_sum : (1 : ℂ) + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0 := cyclotomic5_sum
    have h4_expand : ζ₅^4 = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by
      calc ζ₅^4 = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + (1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4) := by ring
        _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + 0 := by rw [h_zeta_sum]
        _ = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by ring
    rw [h4_expand]
    ring
  rw [h_expand, h_F_eq]
  push_cast
  ring

/-- Key algebraic identity for word3 = A⁻¹B⁻¹A⁻¹BAB acting on E-multiples.

For any point of the form c*E on segment E'E, applying word3 translates it by 2*displacement2*E.

Clockwise convention rotation formulas:
- A⁻¹ = A⁴: z ↦ -1 + ζ₅ * (z + 1)   (net rotation by ζ₅, since A uses ζ₅⁴ and (ζ₅⁴)⁴ = ζ₅)
- B⁻¹ = B⁴: z ↦ 1 + ζ₅ * (z - 1)    (net rotation by ζ₅)
- A: z ↦ -1 + ζ₅⁴ * (z + 1)         (forward clockwise rotation)
- B: z ↦ 1 + ζ₅⁴ * (z - 1)          (forward clockwise rotation)

Word3 = [A⁻¹, B⁻¹, A⁻¹, B, A, B] applied left to right.

With E = ζ₅⁴ - ζ₅³ (clockwise convention):
The translation produced is 2·displacement2·E where displacement2 = (√5-3)/2. -/
lemma word3_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E
    let result := -- A⁻¹ B⁻¹ A⁻¹ B A B applied in complex form
      let step1 := (-1 : ℂ) + ζ₅ * (z + 1)           -- A⁻¹ (ζ₅)
      let step2 := (1 : ℂ) + ζ₅ * (step1 - 1)        -- B⁻¹ (ζ₅)
      let step3 := (-1 : ℂ) + ζ₅ * (step2 + 1)       -- A⁻¹ (ζ₅)
      let step4 := (1 : ℂ) + ζ₅^4 * (step3 - 1)      -- B (ζ₅⁴)
      let step5 := (-1 : ℂ) + ζ₅^4 * (step4 + 1)     -- A (ζ₅⁴)
      (1 : ℂ) + ζ₅^4 * (step5 - 1)                   -- B (ζ₅⁴)
    result = z + (2 * displacement2) • E := by
  intro c _hc
  simp only
  -- Key power reduction lemmas
  have h5 : ζ₅^5 = (1 : ℂ) := zeta5_pow_five
  have h8 : ζ₅^8 = ζ₅^3 := zeta5_pow_eight
  have h12 : ζ₅^12 = ζ₅^2 := zeta5_pow_twelve
  have h13 : ζ₅^13 = ζ₅^3 := zeta5_pow_thirteen
  have h14 : ζ₅^14 = ζ₅^4 := by have := zeta5_pow_reduce 14; norm_num at this; exact this
  have h15 : ζ₅^15 = (1 : ℂ) := zeta5_pow_fifteen
  have h18 : ζ₅^18 = ζ₅^3 := by have := zeta5_pow_reduce 18; norm_num at this; exact this
  have h19 : ζ₅^19 = ζ₅^4 := by have := zeta5_pow_reduce 19; norm_num at this; exact this
  -- sqrt 5 squared equals 5
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- Key identity: 2*displacement2 = √5 - 3
  have h_goldenRatio : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := Real.goldenRatio.eq_1
  have h_one_plus_phi : (1 : ℝ) + Real.goldenRatio = (3 + Real.sqrt 5) / 2 := by
    rw [h_goldenRatio]; ring
  have h_disp2_value : (2 * displacement2 : ℝ) = Real.sqrt 5 - 3 := by
    rw [displacement2_formula]
    rw [h_one_plus_phi]
    have h_ne : (3 + Real.sqrt 5) ≠ 0 := by
      have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
      linarith
    field_simp
    -- Need: (√5 - 3) * (3 + √5) / 2 * 2 = -2 * 2
    -- (√5 - 3)(3 + √5) = 3√5 + 5 - 9 - 3√5 = -4
    have h_prod : (Real.sqrt 5 - 3) * (3 + Real.sqrt 5) = -4 := by
      calc (Real.sqrt 5 - 3) * (3 + Real.sqrt 5)
          = 3 * Real.sqrt 5 + Real.sqrt 5 ^ 2 - 9 - 3 * Real.sqrt 5 := by ring
        _ = 3 * Real.sqrt 5 + 5 - 9 - 3 * Real.sqrt 5 := by rw [hsqrt5_sq]
        _ = -4 := by ring
    linarith
  -- Now unfold and compute with E = ζ₅⁴ - ζ₅³
  unfold E
  -- Convert smul to mul for complex arithmetic
  have hcE : (c : ℂ) • (ζ₅^4 - ζ₅^3) = c * (ζ₅^4 - ζ₅^3) := by rfl
  have h2dE : (2 * displacement2) • (ζ₅^4 - ζ₅^3) =
              (2 * displacement2 : ℝ) * (ζ₅^4 - ζ₅^3) := by rfl
  rw [hcE, h2dE, h_disp2_value]
  -- Use cyclotomic sum identity: 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0
  have h_zeta_sum : (1 : ℂ) + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0 := cyclotomic5_sum
  have h4_expand : ζ₅^4 = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by
    calc ζ₅^4 = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + (1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4) := by ring
      _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + 0 := by rw [h_zeta_sum]
      _ = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by ring
  -- Express √5 in terms of ζ₅: √5 = 1 + 2(ζ₅ + ζ₅⁴)
  have h_sum14 : ζ₅ + ζ₅^4 = ((Real.sqrt 5 - 1) / 2 : ℝ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      rw [zeta5_re, zeta5_pow4_re]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im]
      rw [zeta5_im_eq_sin, zeta5_pow4_im_neg, zeta5_im_eq_sin]
      ring
  have h_sqrt5 : (Real.sqrt 5 : ℂ) = 1 + 2 * (ζ₅ + ζ₅^4) := by
    rw [h_sum14]
    push_cast
    ring
  -- √5 - 3 = 1 + 2(ζ₅ + ζ₅⁴) - 3 = -2 + 2ζ₅ + 2ζ₅⁴
  have h_sqrt5_minus_3 : (Real.sqrt 5 - 3 : ℂ) = -2 + 2 * ζ₅ + 2 * ζ₅^4 := by
    calc (Real.sqrt 5 - 3 : ℂ) = (Real.sqrt 5 : ℂ) - 3 := by simp [sub_eq_add_neg]
      _ = (1 + 2 * (ζ₅ + ζ₅^4)) - 3 := by rw [h_sqrt5]
      _ = -2 + 2 * ζ₅ + 2 * ζ₅^4 := by ring
  -- The full expansion of word3 = A⁻¹B⁻¹A⁻¹BAB
  -- Need to verify the algebraic identity
  -- First expand using ring_nf and reduce high powers
  ring_nf
  simp only [h19, h18, h15, h14, h13, h12, h8]
  -- The goal is now in terms of ζ₅, ζ₅², ζ₅³, ζ₅⁴
  -- Use cyclotomic relation to reduce ζ₅⁴
  rw [h4_expand]
  -- The RHS has ↑(-3 + √5), convert to ζ₅ form
  -- Note: ↑(-3 + √5) = ↑√5 - 3 by push_cast
  have h_neg3_plus : (↑(-3 + Real.sqrt 5) : ℂ) = -2 + 2 * ζ₅ + 2 * ζ₅^4 := by
    have h1 : (↑(-3 + Real.sqrt 5) : ℂ) = (Real.sqrt 5 : ℂ) - 3 := by push_cast; ring
    rw [h1, h_sqrt5]
    ring
  simp only [h_neg3_plus]
  -- RHS still has ζ₅^4 inside the substituted expression, reduce it
  simp only [h4_expand]
  -- ring_nf expands but produces high powers, so reduce those first
  have h6 : ζ₅^6 = ζ₅ := zeta5_pow_six
  -- Reduce high powers then ring
  ring_nf
  simp only [h4_expand, h5, h6]
  -- After simp, we need another ring to finish
  ring_nf

end TDCSG.CompoundSymmetry.GG5
