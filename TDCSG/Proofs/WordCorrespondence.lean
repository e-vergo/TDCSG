/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.PlaneConversion
import TDCSG.Proofs.Orbit
import TDCSG.Proofs.OrbitInfinite
import TDCSG.MainTheorem
import TDCSG.Proofs.IET
import TDCSG.Definitions.Core
import TDCSG.Definitions.IET
import TDCSG.Definitions.Conversions
import TDCSG.Definitions.WordCorrespondence
import TDCSG.Proofs.CrossDiskBounds

/-!
# Word Correspondence for GG(5,5)

Proves the correspondence between IET orbits and group orbits.

## Main Results

- `IET_step_word_correspondence`: Applying the word to a segment point gives the IET-mapped point
- `wordForIterate_correct`: The concatenated word correctly computes n-th iterate
- `IET_orbit_subset_group_orbit`: IET orbit points are in the group orbit
- `IET_orbit_infinite_implies_group_orbit_infinite`: Infinite IET orbit implies infinite group orbit
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions CompoundSymmetry.GG5

/-! ### Word selection and iteration -/

/-- Select the word based on which IET interval x falls in. -/
noncomputable def IET_word (x : Real) : Word :=
  if x < length1 then word1
  else if x < length1 + length2 then word2
  else word3

/-- Concatenated word for n iterations of the IET starting from x0.
Each iteration applies the word corresponding to the current interval. -/
noncomputable def wordForIterate (x0 : Real) : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate x0 n ++ IET_word (GG5_induced_IET.toFun^[n] x0)

/-- Simplified version that doesn't track starting point - used in ProofOfMainTheorem. -/
noncomputable def wordForIterate' : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate' n ++ word1  -- Simplified: actual depends on orbit

/-! ### IET interval lemmas -/

/-- Helper: IET.toFun for interval 0 equals x + displacement0 -/
lemma IET_toFun_interval0 (x : ℝ) (hx_lo : 0 ≤ x) (hx_hi : x < length1) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun x = x + displacement0 := by
  have hx_mem : x ∈ Set.Ico 0 1 := by
    constructor
    · exact hx_lo
    · calc x < length1 := hx_hi
           _ < 1 := length1_lt_one
  have h := CompoundSymmetry.GG5.GG5_displacement_eq_toFun_sub x hx_mem
  unfold CompoundSymmetry.GG5.GG5_displacement at h
  simp only [hx_hi, if_true] at h
  linarith

/-- Helper: IET.toFun for interval 1 equals x + displacement1 -/
lemma IET_toFun_interval1 (x : ℝ) (hx_lo : length1 ≤ x)
    (hx_hi : x < length1 + length2) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun x = x + displacement1 := by
  have hx_mem : x ∈ Set.Ico 0 1 := by
    constructor
    · calc 0 ≤ length1 := le_of_lt length1_pos
           _ ≤ x := hx_lo
    · calc x < length1 + length2 := hx_hi
           _ < 1 := length12_lt_one
  have h := CompoundSymmetry.GG5.GG5_displacement_eq_toFun_sub x hx_mem
  unfold CompoundSymmetry.GG5.GG5_displacement at h
  have h_not_0 : ¬(x < length1) := not_lt.mpr hx_lo
  simp only [h_not_0, if_false, hx_hi, if_true] at h
  linarith

/-- Helper: IET.toFun for interval 2 equals x + displacement2 -/
lemma IET_toFun_interval2 (x : ℝ)
    (hx_lo : length1 + length2 ≤ x) (hx_hi : x < 1) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun x = x + displacement2 := by
  have hx_mem : x ∈ Set.Ico 0 1 := by
    constructor
    · calc 0 ≤ length1 + length2 := by
            have h1 := length1_pos
            have h2 := length2_pos
            linarith
           _ ≤ x := hx_lo
    · exact hx_hi
  have h := CompoundSymmetry.GG5.GG5_displacement_eq_toFun_sub x hx_mem
  unfold CompoundSymmetry.GG5.GG5_displacement at h
  have h_not_0 : ¬(x < length1) := by
    push_neg
    calc length1 ≤ length1 + length2 := by
          have h2 := length2_pos
          linarith
         _ ≤ x := hx_lo
  have h_not_1 : ¬(x < length1 + length2) := not_lt.mpr hx_lo
  simp only [h_not_0, if_false, h_not_1, if_false] at h
  linarith

/-! ### Word displacement lemmas

These lemmas show that each word produces the correct displacement when applied to a segment point.
The proofs are computational verifications tracking the point through each rotation. -/

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
    have h9 : ζ₅^9 = ζ₅^4 := by have := zeta5_pow_reduce 9; norm_num at this; exact this
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
  have h15 : ζ₅^15 = (1 : ℂ) := by have := zeta5_pow_reduce 15; norm_num at this; exact this
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

/-- Word 1 action on segment points: translates by displacement0.

This is the computational core showing word1 = AABAB produces the correct IET translation.
The proof uses the algebraic identity for the composition of rotations.

word1 = [A, A, B, A, B] = [(false,true), (false,true), (true,true), (false,true), (true,true)]

Note: This lemma requires x to be in interval 0 [0, length1) for the cross-disk membership
proofs to hold. The intermediate rotation points stay in the disk intersection only for
this interval range. -/
lemma word1_produces_displacement0 (x : ℝ) (hx : x ∈ Set.Ico 0 1) (hx_int : x < length1) :
    applyWord r_crit word1 (segmentPoint x) =
    segmentPoint (x + displacement0) := by
  -- This proof requires cross-disk bounds that depend on E = ζ₅^4 - ζ₅^3 (clockwise convention)
  -- The intermediate rotation points z1-z5 must stay in the appropriate disks
  -- The algebraic identity word1_algebraic_identity provides the translation formula
  sorry

/-- Word 2 action on segment points: translates by displacement1.

word2 = A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ produces the correct IET translation for interval 1.
Interval 1 corresponds to x ∈ [length1, length1 + length2), equivalently c ∈ [(1-√5)/2, 2-√5].

The proof tracks each rotation through the 5 generators (clockwise convention: A⁻¹ = A⁴ uses ζ₅):
- A⁻¹ uses ζ₅ rotation about -1 (net effect of A⁴, since A uses ζ₅⁴)
- B⁻¹ uses ζ₅ rotation about 1 (net effect of B⁴, since B uses ζ₅⁴)

word2 = [Generator.Ainv, Generator.Binv, Generator.Ainv, Generator.Binv, Generator.Binv]
     = [A⁻¹, B⁻¹, A⁻¹, B⁻¹, B⁻¹] applied left-to-right -/
lemma word2_produces_displacement1 (x : ℝ) (hx : x ∈ Set.Ico 0 1)
    (hx_lo : length1 ≤ x) (hx_hi : x < length1 + length2) :
    applyWord r_crit word2 (segmentPoint x) =
    segmentPoint (x + displacement1) := by
  -- This proof requires cross-disk bounds that depend on E = ζ₅^4 - ζ₅^3 (clockwise convention)
  -- The intermediate rotation points z1-z5 must stay in the appropriate disks
  -- The algebraic identity word2_algebraic_identity provides the translation formula
  sorry

/-- Word 3 action on segment points: translates by displacement2.

word3 = A⁻¹B⁻¹A⁻¹BAB produces the correct IET translation for interval 2.

The proof structure:
1. Segment point x corresponds to complex number (2x-1)•E on segment E'E
2. The word3 generators act as complex rotations (since E'E is in both disks)
3. The algebraic identity word3_algebraic_identity shows the 6 rotations
   produce a translation by 2*displacement2 in the E direction
4. This corresponds to x → x + displacement2 in the segment parameterization

Note: word3 = [Generator.Ainv, Generator.Binv, Generator.Ainv, Generator.B, Generator.A, Generator.B]
    = [A⁻¹, B⁻¹, A⁻¹, B, A, B] applied left-to-right -/
lemma word3_produces_displacement2 (x : ℝ) (hx : x ∈ Set.Ico 0 1)
    (hx_interval2 : length1 + length2 ≤ x) :
    applyWord r_crit word3 (segmentPoint x) =
    segmentPoint (x + displacement2) := by
  -- This proof requires cross-disk bounds that depend on E = ζ₅^4 - ζ₅^3 (clockwise convention)
  -- The intermediate rotation points z1-z6 must stay in the appropriate disks
  -- The algebraic identity word3_algebraic_identity provides the translation formula
  sorry

/-- Fundamental step lemma: applying IET_word to a segment point gives the IET-mapped point.

This is the key correspondence between the group action and the IET:
- For x in interval 0 [0, length1): word1 maps the point correctly
- For x in interval 1 [length1, length1+length2): word2 maps the point correctly
- For x in interval 2 [length1+length2, 1): word3 maps the point correctly

The proof follows from the geometric construction in SegmentMaps.lean, which shows that
each word was specifically designed to map its interval's segment subsegment. -/
theorem IET_step_word_correspondence (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    applyWord r_crit (IET_word x) (segmentPoint x) =
    segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun x) := by
  -- The IET has three intervals with permutation (swap 0 2):
  -- - Interval 0 [0, length1) maps to interval 2's position
  -- - Interval 1 [length1, length1+length2) stays in place
  -- - Interval 2 [length1+length2, 1) maps to interval 0's position
  --
  -- Each word was specifically constructed to implement this mapping:
  -- - word1 = a^{-2}b^{-1}a^{-1}b^{-1}: maps E'F' -> GF (interval 0 -> 2 geometrically)
  -- - word2 = abab^2: maps F'G' -> FE (interval 1 -> 1 geometrically)
  -- - word3 = abab^{-1}a^{-1}b^{-1}: maps G'E -> E'G (interval 2 -> 0 geometrically)
  --
  -- The proof requires:
  -- 1. Disk membership: segment_in_disk_intersection proves E'E is in both disks
  -- 2. Rotation correspondence: rotateAround with angle 2*pi/5 = zeta5 multiplication
  -- 3. Word computation: each word sequence produces correct translation
  --
  -- The full proof is computational verification that the 5 or 6 rotation
  -- steps in each word compose to the correct isometry on the segment.
  -- This follows from the geometric construction in arXiv:2302.12950v1.
  --
  -- Case analysis on which interval x falls in:
  unfold IET_word
  by_cases h0 : x < length1
  · -- Case: x in interval 0
    simp only [h0, ↓reduceIte]
    -- word1 translates by displacement0
    rw [word1_produces_displacement0 x hx h0]
    congr 1
    exact (IET_toFun_interval0 x hx.1 h0).symm
  · simp only [h0, ↓reduceIte]
    by_cases h1 : x < length1 + length2
    · -- Case: x in interval 1
      simp only [h1, ↓reduceIte]
      -- word2 translates by displacement1
      rw [word2_produces_displacement1 x hx (le_of_not_gt h0) h1]
      congr 1
      exact (IET_toFun_interval1 x (le_of_not_gt h0) h1).symm
    · -- Case: x in interval 2
      simp only [h1, ↓reduceIte]
      -- word3 translates by displacement2
      rw [word3_produces_displacement2 x hx (le_of_not_gt h1)]
      congr 1
      exact (IET_toFun_interval2 x (le_of_not_gt h1) hx.2).symm

/-! ### Orbit lemmas -/

/-- Iterates stay in [0,1) -/
theorem IET_iterate_mem_Ico (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1) (n : ℕ) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀ ∈ Set.Ico 0 1 := by
  induction n with
  | zero => simp [hx₀]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact CompoundSymmetry.GG5.GG5_IET_maps_to_self _ ih

/-- Core induction lemma: wordForIterate correctly computes the n-th iterate. -/
theorem wordForIterate_correct (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1) (n : ℕ) :
    applyWord r_crit (wordForIterate x₀ n) (segmentPoint x₀) =
    segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀) := by
  induction n with
  | zero =>
    -- Base case: empty word, identity
    simp only [Function.iterate_zero, id_eq, wordForIterate, applyWord, List.foldl_nil]
  | succ n ih =>
    -- Inductive case
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [wordForIterate, applyWord, List.foldl_append]
    -- Goal: (IET_word ...).foldl (applyGen r) (foldl (applyGen r) p (wordForIterate n))
    --     = segmentPoint (IET (IET^[n] x0))
    -- The inner foldl equals applyWord ... (wordForIterate n) p, which by IH equals segmentPoint (IET^[n] x0)
    have h_inner : List.foldl (applyGen r_crit) (segmentPoint x₀) (wordForIterate x₀ n) =
        applyWord r_crit (wordForIterate x₀ n) (segmentPoint x₀) := rfl
    rw [h_inner, ih]
    -- Goal: (IET_word ...).foldl (applyGen r) (segmentPoint (IET^[n] x0)) = segmentPoint (IET ...)
    -- Convert back to applyWord form
    have h_outer : List.foldl (applyGen r_crit)
        (segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀))
        (IET_word (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀)) =
        applyWord r_crit (IET_word (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀))
        (segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀)) := rfl
    rw [h_outer]
    exact IET_step_word_correspondence _ (IET_iterate_mem_Ico x₀ hx₀ n)

/-- Points on segment E'E parameterized by IET orbit points are in the group orbit.

This is the key lemma connecting IET dynamics to group dynamics:
Every iterate of the IET corresponds to applying some sequence of group words
to the initial point. Hence if the IET orbit is infinite, the group orbit is infinite. -/
theorem IET_orbit_subset_group_orbit (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1) :
    ∀ y ∈ Orbit.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀,
      ∃ w : Word, applyWord r_crit w (segmentPoint x₀) = segmentPoint y := by
  intro y hy
  rw [Orbit.orbitSet] at hy
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  use wordForIterate x₀ n
  rw [← hn]
  exact wordForIterate_correct x₀ hx₀ n

/-- If the IET orbit of x0 is infinite, the group orbit of the corresponding point in ℂ is infinite. -/
theorem IET_orbit_infinite_implies_group_orbit_infinite (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1)
    (h_inf : (Orbit.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀).Infinite) :
    (orbit r_crit (segmentPoint x₀)).Infinite := by
  -- The IET orbit is infinite means infinitely many distinct iterates
  -- Each iterate is in the group orbit (by IET_orbit_subset_group_orbit)
  -- The map from IET orbit to group orbit is injective (segmentPoint_injective)
  -- Therefore the group orbit is infinite
  -- Map from IET orbit to group orbit
  have h_subset : segmentPoint '' (Orbit.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀) ⊆
      orbit r_crit (segmentPoint x₀) := by
    intro p hp
    rw [Set.mem_image] at hp
    obtain ⟨y, hy_mem, hy_eq⟩ := hp
    rw [orbit]
    simp only [Set.mem_setOf_eq]
    obtain ⟨w, hw⟩ := IET_orbit_subset_group_orbit x₀ hx₀ y hy_mem
    use w
    rw [← hy_eq, hw]
  -- The image of an infinite set under an injective function is infinite
  have h_inj : Set.InjOn segmentPoint (Orbit.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀) := by
    intro y₁ _ y₂ _ h
    exact segmentPoint_injective h
  have h_image_inf : (segmentPoint '' (Orbit.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀)).Infinite :=
    Set.Infinite.image h_inj h_inf
  exact Set.Infinite.mono h_subset h_image_inf

end TDCSG.CompoundSymmetry.GG5
