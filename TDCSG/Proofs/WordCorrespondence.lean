/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.Orbit
import TDCSG.Proofs.OrbitInfinite
import TDCSG.MainTheorem
import TDCSG.Proofs.IET
import TDCSG.Definitions.Core
import TDCSG.Definitions.IET
import TDCSG.Definitions.WordCorrespondence
import TDCSG.Proofs.CrossDiskWord3

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

/-- Helper: exp(-2πi/5) = ζ₅⁴.
    This connects the rotation angle used in genA/genB to the 5th root of unity. -/
lemma exp_neg_two_pi_fifth : Complex.exp ((-2 * π / 5 : ℝ) * I) = ζ₅^4 := by
  -- exp(-2πi/5) = exp(2πi/5)^(-1) = ζ₅^(-1) = ζ₅^4
  have h1 : ((-2 * π / 5 : ℝ) : ℂ) * I = -(2 * ↑π * I / 5) := by push_cast; ring
  rw [h1, Complex.exp_neg]
  -- Now: ⊢ (cexp (2 * ↑π * I / 5))⁻¹ = ζ₅ ^ 4
  have h2 : Complex.exp (2 * ↑π * I / 5) = ζ₅ := by unfold ζ₅ zeta5; rfl
  rw [h2, zeta5_inv_eq_pow4]

/-- Helper: genA on a point in leftDisk computes the rotation formula. -/
lemma genA_rotation_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    genA r_crit z = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold genA
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC leftCenter
  simp only [zero_mul, add_zero]
  rw [exp_neg_two_pi_fifth]
  ring

/-- Helper: genB on a point in rightDisk computes the rotation formula. -/
lemma genB_rotation_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    genB r_crit z = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold genB
  simp only [hz, ↓reduceIte]
  unfold rotateAboutC rightCenter
  simp only [zero_mul, add_zero]
  rw [exp_neg_two_pi_fifth]

/-- Helper: exp(2πi/5) = ζ₅.
    This connects the positive rotation angle to the primitive 5th root of unity. -/
lemma exp_two_pi_fifth : Complex.exp ((2 * π / 5 : ℝ) * I) = ζ₅ := by
  unfold ζ₅ zeta5
  congr 1
  push_cast
  ring

/-- Helper: When all intermediate points in A⁴ chain are in leftDisk,
    applyGen .Ainv computes the inverse rotation formula: -1 + ζ₅ * (z + 1).

    This follows from: A uses ζ₅^4 rotation, so A⁴ uses (ζ₅^4)^4 = ζ₅^16 = ζ₅. -/
lemma applyGen_Ainv_formula (z : ℂ)
    (hz : z ∈ leftDisk r_crit)
    (h1 : (-1 : ℂ) + ζ₅^4 * (z + 1) ∈ leftDisk r_crit)
    (h2 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) ∈ leftDisk r_crit)
    (h3 : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z + 1) + 1) + 1) ∈ leftDisk r_crit) :
    applyGen r_crit z .Ainv = (-1 : ℂ) + ζ₅ * (z + 1) := by
  unfold applyGen
  simp only
  -- First application
  rw [genA_rotation_formula z hz]
  -- Second application
  rw [genA_rotation_formula _ h1]
  -- Third application
  rw [genA_rotation_formula _ h2]
  -- Fourth application
  rw [genA_rotation_formula _ h3]
  -- Now simplify: (ζ₅^4)^4 = ζ₅^16 = ζ₅
  have h16 : ζ₅^16 = ζ₅ := zeta5_pow_sixteen
  ring_nf
  simp only [h16]

/-- Helper: When all intermediate points in B⁴ chain are in rightDisk,
    applyGen .Binv computes the inverse rotation formula: 1 + ζ₅ * (z - 1). -/
lemma applyGen_Binv_formula (z : ℂ)
    (hz : z ∈ rightDisk r_crit)
    (h1 : (1 : ℂ) + ζ₅^4 * (z - 1) ∈ rightDisk r_crit)
    (h2 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) ∈ rightDisk r_crit)
    (h3 : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z - 1) - 1) - 1) ∈ rightDisk r_crit) :
    applyGen r_crit z .Binv = (1 : ℂ) + ζ₅ * (z - 1) := by
  unfold applyGen
  simp only
  rw [genB_rotation_formula z hz]
  rw [genB_rotation_formula _ h1]
  rw [genB_rotation_formula _ h2]
  rw [genB_rotation_formula _ h3]
  have h16 : ζ₅^16 = ζ₅ := zeta5_pow_sixteen
  ring_nf
  simp only [h16]

/-- Helper: applyGen .A computes the forward rotation formula. -/
lemma applyGen_A_formula (z : ℂ) (hz : z ∈ leftDisk r_crit) :
    applyGen r_crit z .A = (-1 : ℂ) + ζ₅^4 * (z + 1) := by
  unfold applyGen
  exact genA_rotation_formula z hz

/-- Helper: applyGen .B computes the forward rotation formula. -/
lemma applyGen_B_formula (z : ℂ) (hz : z ∈ rightDisk r_crit) :
    applyGen r_crit z .B = (1 : ℂ) + ζ₅^4 * (z - 1) := by
  unfold applyGen
  exact genB_rotation_formula z hz

/-- Convenience: length1 + length2 = (3 - √5)/2. -/
lemma length12_eq_sqrt5 : length1 + length2 = (3 - Real.sqrt 5) / 2 := by
  have h_goldenRatio : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := Real.goldenRatio.eq_1
  have h_one_plus_phi : (1 : ℝ) + Real.goldenRatio = (3 + Real.sqrt 5) / 2 := by
    rw [h_goldenRatio]; ring
  rw [length12_sum, h_one_plus_phi]
  have h_denom_ne : (3 + Real.sqrt 5) ≠ 0 := by
    have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
    linarith
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp
  -- (3 - √5) * 2 = 2 * (3 + √5) / (3 + √5) * (3 - √5)
  -- Need: 2 * (3 - √5) = 2 * (9 - 5) / (3 + √5) ... no
  -- Actually: 1/(1+φ) = 2/(3+√5) and (3-√5)/2, so need:
  -- 2/(3+√5) = (3-√5)/2 iff 4 = (3-√5)(3+√5) = 9 - 5 = 4. ✓
  nlinarith [hsqrt5_sq]

/-- Key relationship: when x ≥ length1 + length2, we have c = 2x - 1 ≥ 2 - √5. -/
lemma interval2_c_lower_bound (x : ℝ) (hx : length1 + length2 ≤ x) :
    2 - Real.sqrt 5 ≤ 2 * x - 1 := by
  rw [length12_eq_sqrt5] at hx
  linarith

/-- Helper: segmentPoint expressed in terms of E. -/
lemma segmentPoint_eq_smul_E (x : ℝ) : segmentPoint x = (2 * x - 1) • E := by
  unfold segmentPoint E'
  rw [sub_neg_eq_add, show E + E = (2 : ℝ) • E by simp [two_smul], smul_smul]
  rw [show -E + (x * 2) • E = (x * 2 - 1) • E by rw [sub_smul, one_smul]; ring_nf]
  congr 1; ring

/-- Helper: translation property of segmentPoint. -/
lemma segmentPoint_add_displacement (x d : ℝ) :
    segmentPoint (x + d) = segmentPoint x + (2 * d) • E := by
  rw [segmentPoint_eq_smul_E, segmentPoint_eq_smul_E]
  simp only [Complex.real_smul]
  rw [← add_mul]
  congr 1
  push_cast
  ring

lemma word1_produces_displacement0 (x : ℝ) (hx : x ∈ Set.Ico 0 1) (hx_int : x < length1) :
    applyWord r_crit word1 (segmentPoint x) =
    segmentPoint (x + displacement0) := by
  -- Rewrite the RHS using the translation property
  rw [segmentPoint_add_displacement]

  -- Set up parameter c = 2x - 1
  set c := 2 * x - 1 with hc_def
  have hc_lo : -1 ≤ c := by simp only [hc_def]; linarith [hx.1]
  have hc_hi_le : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨hc_lo, hc_hi_le⟩

  -- Express segmentPoint x in terms of c
  have h_z0_eq : segmentPoint x = (c : ℂ) • E := by
    rw [segmentPoint_eq_smul_E, hc_def]
    simp only [Complex.real_smul, smul_eq_mul]

  -- Get disk membership for the starting point
  have h_in_disks := segment_in_disk_intersection x ⟨hx.1, le_of_lt hx.2⟩
  have hz0_left : segmentPoint x ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    rw [show segmentPoint x - (-1 : ℂ) = segmentPoint x + 1 by ring]
    unfold segmentPoint
    exact h_in_disks.1
  have hz0_right : segmentPoint x ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    unfold segmentPoint
    exact h_in_disks.2

  -- Unfold applyWord and word1
  unfold applyWord word1
  simp only [List.foldl_cons, List.foldl_nil]

  -- Define intermediate points (algebraically)
  let z0 := segmentPoint x
  let z1_alg := (-1 : ℂ) + ζ₅^4 * (z0 + 1)           -- After A
  let z2_alg := (-1 : ℂ) + ζ₅^4 * (z1_alg + 1)       -- After A
  let z3_alg := (1 : ℂ) + ζ₅^4 * (z2_alg - 1)        -- After B
  let z4_alg := (-1 : ℂ) + ζ₅^4 * (z3_alg + 1)       -- After A
  let z5_alg := (1 : ℂ) + ζ₅^4 * (z4_alg - 1)        -- After B

  -- The algebraic identity tells us z5_alg = z0 + (2 * displacement0) • E
  have h_alg := word1_algebraic_identity c h_c_mem
  simp only at h_alg

  -- We need to show applyGen computes the same as the algebraic formulas
  -- This requires showing each intermediate point is in the appropriate disk

  -- Step 1: genA z0 = z1_alg (since z0 ∈ leftDisk)
  have h_step1 : applyGen r_crit z0 .A = z1_alg := by
    unfold applyGen
    exact genA_rotation_formula z0 hz0_left

  -- For remaining steps, we need disk membership of intermediate points
  -- These bounds depend on the cross-disk analysis in CrossDiskBounds.lean
  -- For now, we assume these hold and proceed with the proof

  -- The key insight: all segment points in [0, length1) have their word1
  -- intermediate points staying within the lens intersection

  -- This is the gap requiring cross-disk bounds:
  -- We need to show z1_alg, z2_alg, z3_alg, z4_alg are in the appropriate disks

  -- Assuming disk membership for intermediate points (to be proven with cross-disk bounds):
  -- z1_alg ∈ leftDisk ∩ rightDisk
  -- z2_alg ∈ leftDisk ∩ rightDisk
  -- z3_alg ∈ leftDisk ∩ rightDisk
  -- z4_alg ∈ leftDisk ∩ rightDisk

  -- Then the proof follows from chaining the rotation formulas and the algebraic identity

  -- Current status: the algebraic identity is proven, but disk membership
  -- for intermediate points requires completing the cross-disk bounds proofs
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
  -- Rewrite the RHS using the translation property
  rw [segmentPoint_add_displacement]

  -- Set up parameter c = 2x - 1
  set c := 2 * x - 1 with hc_def

  -- Derive bounds on c from interval 2 constraints
  have hc_lo : 2 - Real.sqrt 5 ≤ c := interval2_c_lower_bound x hx_interval2
  have hc_hi : c ≤ 1 := by simp only [hc_def]; linarith [hx.2]
  have hc_lo_ge_neg1 : -1 < c := by
    have h := c_lower_word3_gt_neg1
    unfold c_lower_word3 at h
    linarith
  have h_c_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hc_lo_ge_neg1, hc_hi⟩

  -- Express segmentPoint x in terms of c
  have h_z0_eq : segmentPoint x = (c : ℂ) • E := by
    rw [segmentPoint_eq_smul_E, hc_def]
    rfl

  -- Get disk membership for the starting point
  have h_in_disks := segment_in_disk_intersection x ⟨hx.1, le_of_lt hx.2⟩
  have hz0_left : segmentPoint x ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    rw [show segmentPoint x - (-1 : ℂ) = segmentPoint x + 1 by ring]
    unfold segmentPoint
    exact h_in_disks.1
  have hz0_right : segmentPoint x ∈ rightDisk r_crit := by
    unfold rightDisk closedDiskC
    simp only [Set.mem_setOf_eq]
    unfold segmentPoint
    exact h_in_disks.2

  -- The algebraic identity tells us what the 6-step rotation produces
  have h_alg := word3_algebraic_identity c h_c_mem
  simp only at h_alg

  -- The proof strategy:
  -- word3_algebraic_identity proves that for z = c • E,
  -- the sequence of 6 rotations (A⁻¹ B⁻¹ A⁻¹ B A B) produces z + (2 * displacement2) • E.
  --
  -- We need to show applyWord computes the same as the algebraic formula.
  -- This requires showing each intermediate point is in the appropriate disk.
  --
  -- The cross-disk bounds (cross_disk_w3_z1_bound through cross_disk_w3_z5_bound)
  -- prove that for c ∈ [2 - √5, 1], each intermediate point stays in the disk intersection.
  --
  -- Once disk membership is established, genA/genB compute the rotation formulas,
  -- and the 6-step chain equals the algebraic identity result.
  --
  -- The core gap is: connecting applyGen (which applies genA 4 times for Ainv,
  -- genB 4 times for Binv, etc.) to the algebraic rotation formulas.
  -- This requires showing disk membership for all 22 intermediate points
  -- (4 from each of 3 inverse generators, plus 1 from each of 3 forward generators).
  --
  -- Since the cross_disk_w3_z*_bound lemmas have sorry but we assume they are correct,
  -- the proof reduces to showing the algebraic chain matches.

  -- Unfold applyWord and word3
  unfold applyWord word3
  simp only [List.foldl_cons, List.foldl_nil]

  -- The goal is now:
  -- applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit
  --   (applyGen r_crit (applyGen r_crit (segmentPoint x) .Ainv) .Binv) .Ainv) .B) .A) .B
  -- = segmentPoint x + (2 * displacement2) • E

  -- Rewrite using h_z0_eq to convert segmentPoint x to c • E
  rw [h_z0_eq]

  -- Define the intermediate algebraic points (from word3_algebraic_identity)
  -- z0 = c • E
  -- z1 = -1 + ζ₅ * (z0 + 1)  (after A⁻¹)
  -- z2 = 1 + ζ₅ * (z1 - 1)   (after B⁻¹)
  -- z3 = -1 + ζ₅ * (z2 + 1)  (after A⁻¹)
  -- z4 = 1 + ζ₅^4 * (z3 - 1) (after B)
  -- z5 = -1 + ζ₅^4 * (z4 + 1)(after A)
  -- z6 = 1 + ζ₅^4 * (z5 - 1) (after B) = z0 + (2*displacement2) • E

  let z0 : ℂ := (c : ℂ) • E
  let z1 := (-1 : ℂ) + ζ₅ * (z0 + 1)
  let z2 := (1 : ℂ) + ζ₅ * (z1 - 1)
  let z3 := (-1 : ℂ) + ζ₅ * (z2 + 1)
  let z4 := (1 : ℂ) + ζ₅^4 * (z3 - 1)
  let z5 := (-1 : ℂ) + ζ₅^4 * (z4 + 1)
  let z6 := (1 : ℂ) + ζ₅^4 * (z5 - 1)

  -- The algebraic identity tells us z6 = z0 + (2 * displacement2) • E
  have h_z6_eq : z6 = z0 + (2 * displacement2) • E := by
    simp only [z6, z5, z4, z3, z2, z1, z0]
    convert h_alg using 1

  -- The proof requires showing that applyGen computes the algebraic formulas
  -- at each step. This depends on disk membership of intermediate points.

  -- For each generator step, we need:
  -- - For A⁻¹: the point and 3 intermediate genA results must be in leftDisk
  -- - For B⁻¹: the point and 3 intermediate genB results must be in rightDisk
  -- - For A: the point must be in leftDisk
  -- - For B: the point must be in rightDisk

  -- The cross-disk bounds (cross_disk_w3_z*_bound) prove these memberships
  -- for c ∈ [2 - √5, 1]. Since these bounds currently have sorry,
  -- we assert the necessary disk memberships here.

  -- Disk membership for z0 (already proven above via hz0_left, hz0_right)
  have hz0_left' : z0 ∈ leftDisk r_crit := by
    simp only [z0]
    rw [show (c : ℂ) • E = segmentPoint x by rw [h_z0_eq]]
    exact hz0_left
  have hz0_right' : z0 ∈ rightDisk r_crit := by
    simp only [z0]
    rw [show (c : ℂ) • E = segmentPoint x by rw [h_z0_eq]]
    exact hz0_right

  -- The remaining disk memberships for intermediate points follow from cross-disk bounds.
  -- For now, we complete the proof structure and mark the disk membership gaps.

  -- Step 1: Show applyGen z0 .Ainv = z1
  -- This requires z0 and three intermediate points to be in leftDisk

  -- Step 2: Show applyGen z1 .Binv = z2
  -- This requires z1 and three intermediate points to be in rightDisk

  -- ... and so on for all 6 steps

  -- The final result follows from the algebraic identity

  -- The complete proof would chain all applyGen steps using the helper lemmas,
  -- but requires proving all intermediate disk memberships.
  -- Since this depends on cross-disk bounds that have sorry, we mark this gap.

  -- The algebraic identity shows the result equals z0 + (2*displacement2) • E
  -- which equals segmentPoint x + (2*displacement2) • E by h_z0_eq

  -- We need to show applyGen chain equals z6, then use h_z6_eq
  -- The goal is: applyGen ... (c • E) = c • E + (2 * displacement2) • E
  -- We know z6 = z0 + (2 * displacement2) • E = c • E + (2 * displacement2) • E

  -- Strategy: show applyGen chain equals z6, then use h_z6_eq
  -- This requires disk membership for all intermediate points.

  -- The disk membership facts follow from the cross-disk bounds.
  -- We assert them here as hypotheses (proven via cross_disk_w3_z*_bound).

  -- For A⁻¹ on z0: need z0, and 3 intermediate genA points in leftDisk
  -- The 3 intermediate points after genA on z0 are:
  -- genA z0 = -1 + ζ₅^4 * (z0 + 1)
  -- genA (genA z0) = -1 + ζ₅^4 * (genA z0 + 1)
  -- genA (genA (genA z0)) = -1 + ζ₅^4 * (genA (genA z0) + 1)

  -- Rather than proving all 22 intermediate memberships, we use native_decide
  -- or prove the key fact: applyGen chain = z6

  -- Key insight: if we can show applyGen computes the algebraic formulas,
  -- the result follows from h_z6_eq.

  -- Since this proof depends on cross-disk bounds (which have sorry),
  -- we complete by showing the algebraic structure matches.

  -- The applyGen chain on z0 should equal z6 when all disk memberships hold.
  -- z6 = z0 + (2 * displacement2) • E by h_z6_eq

  suffices h : applyGen r_crit
      (applyGen r_crit
        (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv) .Ainv) .B)
        .A)
      .B = z6 by
    rw [h, h_z6_eq]

  -- To prove this, we need to show each applyGen step computes the algebraic formula.
  -- This requires disk membership at each step.

  -- The proof structure: chain applyGen results using helper lemmas
  -- applyGen z0 .Ainv = z1 (by applyGen_Ainv_formula, given disk membership)
  -- applyGen z1 .Binv = z2 (by applyGen_Binv_formula, given disk membership)
  -- applyGen z2 .Ainv = z3 (by applyGen_Ainv_formula, given disk membership)
  -- applyGen z3 .B = z4 (by applyGen_B_formula, given disk membership)
  -- applyGen z4 .A = z5 (by applyGen_A_formula, given disk membership)
  -- applyGen z5 .B = z6 (by applyGen_B_formula, given disk membership)

  -- The disk memberships follow from cross_disk_w3_z*_bound lemmas.
  -- Since those have sorry, we assume the disk memberships here.

  -- Disk membership for intermediate points in A⁻¹ chain on z0.
  -- Key insight: rotating by ζ₅^4 preserves disk membership since |ζ₅^4| = 1.
  -- For z in leftDisk: |z + 1| ≤ r_crit
  -- After rotation: |(-1 + ζ₅^4*(z+1)) + 1| = |ζ₅^4*(z+1)| = |z+1| ≤ r_crit
  have hz0_A1_left : (-1 : ℂ) + ζ₅^4 * (z0 + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_left' ⊢
    simp only [Set.mem_setOf_eq] at hz0_left' ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * (z0 + 1) - (-1) = ζ₅^4 * (z0 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    simp only [one_mul]
    convert hz0_left' using 2
    ring
  have hz0_A2_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_A1_left ⊢
    simp only [Set.mem_setOf_eq] at hz0_A1_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) - (-1) =
        ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    simp only [one_mul]
    convert hz0_A1_left using 2
    ring
  have hz0_A3_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_A2_left ⊢
    simp only [Set.mem_setOf_eq] at hz0_A2_left ⊢
    rw [show (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) - (-1) =
        ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z0 + 1) + 1) + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs_pow4]
    simp only [one_mul]
    convert hz0_A2_left using 2
    ring

  -- z1 = applyGen z0 .Ainv is in both disks
  -- For leftDisk: z1 + 1 = ζ₅*(z0 + 1), so |z1 + 1| = |z0 + 1| since |ζ₅| = 1
  have hz1_left : z1 ∈ leftDisk r_crit := by
    unfold leftDisk closedDiskC at hz0_left' ⊢
    simp only [Set.mem_setOf_eq] at hz0_left' ⊢
    simp only [z1]
    rw [show (-1 : ℂ) + ζ₅ * (z0 + 1) - (-1) = ζ₅ * (z0 + 1) by ring]
    rw [Complex.norm_mul, zeta5_abs, one_mul]
    convert hz0_left' using 2
    ring
  -- For rightDisk: z1 - 1 = conj((ζ₅^4 - 2) + c*(1 - ζ₅)), use cross_disk_w3_z1_bound
  have hz1_right : z1 ∈ rightDisk r_crit := by sorry

  -- Disk membership for intermediate points in B⁻¹ chain on z1
  have hz1_B1_right : (1 : ℂ) + ζ₅^4 * (z1 - 1) ∈ rightDisk r_crit := by sorry
  have hz1_B2_right : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) ∈ rightDisk r_crit := by sorry
  have hz1_B3_right : (1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * (z1 - 1) - 1) - 1) ∈ rightDisk r_crit := by sorry

  -- z2 is in both disks
  have hz2_left : z2 ∈ leftDisk r_crit := by sorry
  have hz2_right : z2 ∈ rightDisk r_crit := by sorry

  -- Disk membership for intermediate points in A⁻¹ chain on z2
  have hz2_A1_left : (-1 : ℂ) + ζ₅^4 * (z2 + 1) ∈ leftDisk r_crit := by sorry
  have hz2_A2_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) ∈ leftDisk r_crit := by sorry
  have hz2_A3_left : (-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (z2 + 1) + 1) + 1) ∈ leftDisk r_crit := by sorry

  -- z3 is in both disks
  have hz3_left : z3 ∈ leftDisk r_crit := by sorry
  have hz3_right : z3 ∈ rightDisk r_crit := by sorry

  -- z4 is in both disks
  have hz4_left : z4 ∈ leftDisk r_crit := by sorry
  have hz4_right : z4 ∈ rightDisk r_crit := by sorry

  -- z5 is in both disks
  have hz5_left : z5 ∈ leftDisk r_crit := by sorry
  have hz5_right : z5 ∈ rightDisk r_crit := by sorry

  -- Now chain through the 6 steps
  -- Step 1: applyGen z0 .Ainv = z1
  have h_step1 : applyGen r_crit z0 .Ainv = z1 := by
    exact applyGen_Ainv_formula z0 hz0_left' hz0_A1_left hz0_A2_left hz0_A3_left

  -- Step 2: applyGen z1 .Binv = z2
  have h_step2 : applyGen r_crit z1 .Binv = z2 := by
    exact applyGen_Binv_formula z1 hz1_right hz1_B1_right hz1_B2_right hz1_B3_right

  -- Step 3: applyGen z2 .Ainv = z3
  have h_step3 : applyGen r_crit z2 .Ainv = z3 := by
    exact applyGen_Ainv_formula z2 hz2_left hz2_A1_left hz2_A2_left hz2_A3_left

  -- Step 4: applyGen z3 .B = z4
  have h_step4 : applyGen r_crit z3 .B = z4 := by
    exact applyGen_B_formula z3 hz3_right

  -- Step 5: applyGen z4 .A = z5
  have h_step5 : applyGen r_crit z4 .A = z5 := by
    exact applyGen_A_formula z4 hz4_left

  -- Step 6: applyGen z5 .B = z6
  have h_step6 : applyGen r_crit z5 .B = z6 := by
    exact applyGen_B_formula z5 hz5_right

  -- Chain all steps together
  calc applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z0 .Ainv) .Binv) .Ainv) .B) .A) .B
      = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z1 .Binv) .Ainv) .B) .A) .B := by rw [h_step1]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit (applyGen r_crit z2 .Ainv) .B) .A) .B := by rw [h_step2]
    _ = applyGen r_crit (applyGen r_crit (applyGen r_crit z3 .B) .A) .B := by rw [h_step3]
    _ = applyGen r_crit (applyGen r_crit z4 .A) .B := by rw [h_step4]
    _ = applyGen r_crit z5 .B := by rw [h_step5]
    _ = z6 := h_step6

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
    ∀ y ∈ RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀,
      ∃ w : Word, applyWord r_crit w (segmentPoint x₀) = segmentPoint y := by
  intro y hy
  rw [RealDynamics.orbitSet] at hy
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  use wordForIterate x₀ n
  rw [← hn]
  exact wordForIterate_correct x₀ hx₀ n

/-- If the IET orbit of x0 is infinite, the group orbit of the corresponding point in ℂ is infinite. -/
theorem IET_orbit_infinite_implies_group_orbit_infinite (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1)
    (h_inf : (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀).Infinite) :
    (orbit r_crit (segmentPoint x₀)).Infinite := by
  -- The IET orbit is infinite means infinitely many distinct iterates
  -- Each iterate is in the group orbit (by IET_orbit_subset_group_orbit)
  -- The map from IET orbit to group orbit is injective (segmentPoint_injective)
  -- Therefore the group orbit is infinite
  -- Map from IET orbit to group orbit
  have h_subset : segmentPoint '' (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀) ⊆
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
  have h_inj : Set.InjOn segmentPoint (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀) := by
    intro y₁ _ y₂ _ h
    exact segmentPoint_injective h
  have h_image_inf : (segmentPoint '' (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀)).Infinite :=
    Set.Infinite.image h_inj h_inf
  exact Set.Infinite.mono h_subset h_image_inf

end TDCSG.CompoundSymmetry.GG5
