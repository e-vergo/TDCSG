/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points
import TDCSG.Definitions.WordCorrespondence
import TDCSG.Proofs.Zeta5
import TDCSG.Proofs.IET

/-!
# Algebraic Identities for IET Words

This file proves algebraic identities showing that applying the three IET words (word1, word2,
word3) to points on the segment produces the correct displacements.

## Main results

- `word1_algebraic_identity`: Word1 produces the correct algebraic displacement
- `word2_algebraic_identity`: Word2 produces the correct algebraic displacement
- `word3_algebraic_identity`: Word3 produces the correct algebraic displacement

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions CompoundSymmetry.GG5

lemma word1_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E
    let result :=
      let step1 := (-1 : ℂ) + ζ₅^4 * (z + 1)
      let step2 := (-1 : ℂ) + ζ₅^4 * (step1 + 1)
      let step3 := (1 : ℂ) + ζ₅^4 * (step2 - 1)
      let step4 := (-1 : ℂ) + ζ₅^4 * (step3 + 1)
      (1 : ℂ) + ζ₅^4 * (step4 - 1)
    result = z + (2 * displacement0) • E := by
  intro c _hc
  simp only

  have h_sum1 : ζ₅ + ζ₅^4 = ((Real.sqrt 5 - 1) / 2 : ℝ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      rw [zeta5_re, zeta5_pow4_re]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im]
      rw [zeta5_im_eq_sin, zeta5_pow4_im_neg, zeta5_im_eq_sin]
      ring

  have h_F_eq : (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 = (1 / Real.goldenRatio : ℝ) * (ζ₅^4 - ζ₅^3) := by

    have h_factor : (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) = (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 := by
      calc (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3)
          = ζ₅^5 - ζ₅^4 + ζ₅^8 - ζ₅^7 := by ring
        _ = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 := by simp only [zeta5_pow_five, zeta5_pow_eight, zeta5_pow_seven]
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
              _ = Real.sqrt 5 + 5 - 1 - Real.sqrt 5 := by rw [sqrt5_sq]
              _ = 4 := by ring
          field_simp
          linarith

  unfold displacement0 length3 E

  have hcE : (c : ℂ) • (ζ₅^4 - ζ₅^3) = c * (ζ₅^4 - ζ₅^3) := by rfl
  have h2dE : (2 * (1 / Real.goldenRatio)) • (ζ₅^4 - ζ₅^3) =
              (2 * (1 / Real.goldenRatio) : ℝ) * (ζ₅^4 - ζ₅^3) := by rfl
  rw [hcE, h2dE]

  have h_expand : (1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * ((-1 : ℂ) + ζ₅^4 * (↑c * (ζ₅^4 - ζ₅^3) + 1) + 1) - 1) + 1) - 1)
      = ↑c * (ζ₅^4 - ζ₅^3) + 2 * ((1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2) := by
    ring_nf

    simp only [zeta5_pow_twentyfour, zeta5_pow_twentythree, zeta5_pow_twenty_C, zeta5_pow_twelve, zeta5_pow_eight]

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

lemma word2_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E
    let result :=
      let step1 := (-1 : ℂ) + ζ₅ * (z + 1)
      let step2 := (1 : ℂ) + ζ₅ * (step1 - 1)
      let step3 := (-1 : ℂ) + ζ₅ * (step2 + 1)
      let step4 := (1 : ℂ) + ζ₅ * (step3 - 1)
      (1 : ℂ) + ζ₅ * (step4 - 1)
    result = z + (2 * displacement1) • E := by
  intro c _hc
  simp only

  have h_disp : displacement1 = 1 / Real.goldenRatio := by
    rw [displacement0_eq_displacement1.symm]
    unfold displacement0 length3
    ring

  have h_sum1 : ζ₅ + ζ₅^4 = ((Real.sqrt 5 - 1) / 2 : ℝ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      rw [zeta5_re, zeta5_pow4_re]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im]
      rw [zeta5_im_eq_sin, zeta5_pow4_im_neg, zeta5_im_eq_sin]
      ring

  have h_F_eq : (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 = (1 / Real.goldenRatio : ℝ) * (ζ₅^4 - ζ₅^3) := by

    have h_factor : (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3) = (1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2 := by
      calc (ζ₅ + ζ₅^4) * (ζ₅^4 - ζ₅^3)
          = ζ₅^5 - ζ₅^4 + ζ₅^8 - ζ₅^7 := by ring
        _ = 1 - ζ₅^4 + ζ₅^3 - ζ₅^2 := by simp only [zeta5_pow_five, zeta5_pow_eight, zeta5_pow_seven]
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
              _ = Real.sqrt 5 + 5 - 1 - Real.sqrt 5 := by rw [sqrt5_sq]
              _ = 4 := by ring
          field_simp
          linarith

  unfold displacement1 length3 E

  have hcE : (c : ℂ) • (ζ₅^4 - ζ₅^3) = c * (ζ₅^4 - ζ₅^3) := by rfl
  have h2dE : (2 * (1 / Real.goldenRatio)) • (ζ₅^4 - ζ₅^3) =
              (2 * (1 / Real.goldenRatio) : ℝ) * (ζ₅^4 - ζ₅^3) := by rfl
  rw [hcE, h2dE]

  have h_expand : (1 : ℂ) + ζ₅ * ((1 : ℂ) + ζ₅ * ((-1 : ℂ) + ζ₅ * ((1 : ℂ) + ζ₅ * ((-1 : ℂ) + ζ₅ * (↑c * (ζ₅^4 - ζ₅^3) + 1) - 1) + 1) - 1) - 1)
      = ↑c * (ζ₅^4 - ζ₅^3) + 2 * ((1 : ℂ) - ζ₅^4 + ζ₅^3 - ζ₅^2) := by
    ring_nf

    simp only [zeta5_pow_nine, zeta5_pow_eight, zeta5_pow_five]

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

lemma word3_algebraic_identity :
    ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
    let z := (c : ℂ) • E
    let result :=
      let step1 := (-1 : ℂ) + ζ₅ * (z + 1)
      let step2 := (1 : ℂ) + ζ₅ * (step1 - 1)
      let step3 := (-1 : ℂ) + ζ₅ * (step2 + 1)
      let step4 := (1 : ℂ) + ζ₅^4 * (step3 - 1)
      let step5 := (-1 : ℂ) + ζ₅^4 * (step4 + 1)
      (1 : ℂ) + ζ₅^4 * (step5 - 1)
    result = z + (2 * displacement2) • E := by
  intro c _hc
  simp only

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

    have h_prod : (Real.sqrt 5 - 3) * (3 + Real.sqrt 5) = -4 := by
      calc (Real.sqrt 5 - 3) * (3 + Real.sqrt 5)
          = 3 * Real.sqrt 5 + Real.sqrt 5 ^ 2 - 9 - 3 * Real.sqrt 5 := by ring
        _ = 3 * Real.sqrt 5 + 5 - 9 - 3 * Real.sqrt 5 := by rw [sqrt5_sq]
        _ = -4 := by ring
    linarith

  unfold E

  have hcE : (c : ℂ) • (ζ₅^4 - ζ₅^3) = c * (ζ₅^4 - ζ₅^3) := by rfl
  have h2dE : (2 * displacement2) • (ζ₅^4 - ζ₅^3) =
              (2 * displacement2 : ℝ) * (ζ₅^4 - ζ₅^3) := by rfl
  rw [hcE, h2dE, h_disp2_value]

  have h_zeta_sum : (1 : ℂ) + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4 = 0 := cyclotomic5_sum
  have h4_expand : ζ₅^4 = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by
    calc ζ₅^4 = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + (1 + ζ₅ + ζ₅^2 + ζ₅^3 + ζ₅^4) := by ring
      _ = -(1 + ζ₅ + ζ₅^2 + ζ₅^3) + 0 := by rw [h_zeta_sum]
      _ = -1 - ζ₅ - ζ₅^2 - ζ₅^3 := by ring

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

  have h_sqrt5_minus_3 : (Real.sqrt 5 - 3 : ℂ) = -2 + 2 * ζ₅ + 2 * ζ₅^4 := by
    calc (Real.sqrt 5 - 3 : ℂ) = (Real.sqrt 5 : ℂ) - 3 := by simp [sub_eq_add_neg]
      _ = (1 + 2 * (ζ₅ + ζ₅^4)) - 3 := by rw [h_sqrt5]
      _ = -2 + 2 * ζ₅ + 2 * ζ₅^4 := by ring

  ring_nf
  simp only [zeta5_pow_nineteen, zeta5_pow_eighteen, zeta5_pow_fifteen, zeta5_pow_fourteen, zeta5_pow_thirteen, zeta5_pow_twelve, zeta5_pow_eight]

  rw [h4_expand]

  have h_neg3_plus : (↑(-3 + Real.sqrt 5) : ℂ) = -2 + 2 * ζ₅ + 2 * ζ₅^4 := by
    have h1 : (↑(-3 + Real.sqrt 5) : ℂ) = (Real.sqrt 5 : ℂ) - 3 := by push_cast; ring
    rw [h1, h_sqrt5]
    ring
  simp only [h_neg3_plus]

  simp only [h4_expand]

  ring_nf
  simp only [h4_expand, zeta5_pow_five, zeta5_pow_six]

  ring_nf

end TDCSG.CompoundSymmetry.GG5
