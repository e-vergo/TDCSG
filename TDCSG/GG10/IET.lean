/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.GG10.Core
import TDCSG.Definitions.IET
import TDCSG.Definitions.WordCorrespondence

/-!
# 2-Interval Exchange Transformation for GG(10,10)

This file defines the 2-interval IET induced by the GG(10,10) group action at the
critical radius r_crit_10 = √(4-φ).

## Main definitions

- `length1_10`, `length2_10`: The two interval lengths (1/φ and 1 - 1/φ)
- `GG10_induced_IET`: The 2-interval IET induced by GG10 at r_crit_10
- `word1_10`, `word2_10`: The generator words for each interval
- `IET_word_10 x`: The word corresponding to applying the IET to point x

## Key difference from GG5

Unlike GG5's 3-interval cyclic permutation, GG10 induces a simpler 2-interval IET
that is conjugate to rotation by 1/φ on the circle. This makes the infiniteness
proof more direct: since 1/φ is irrational, all orbits are dense (hence infinite).

## Structure

- J₁ = [0, 1/φ): translated by +0.382 = 2-φ via w₁ = a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³
- J₂ = [1/φ, 1): translated by -0.618 = -1/φ via w₂ = a⁻¹b⁻¹ab

The permutation swaps the two intervals: 0 ↔ 1.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.GG10

open Real
open TDCSG.Definitions (φ Generator Word)

/-! ### Interval Lengths -/

/-- The length of the first interval J₁ = [0, 1/φ).

This is 1/φ ≈ 0.618, which is the golden ratio conjugate.
Since φ² = φ + 1, we have 1/φ = φ - 1. -/
noncomputable def length1_10 : ℝ := 1 / φ

/-- The length of the second interval J₂ = [1/φ, 1).

This is 1 - 1/φ = (φ-1)/φ ≈ 0.382.
Note: (φ-1)/φ = 1/φ² = 2 - φ. -/
noncomputable def length2_10 : ℝ := 1 - 1 / φ

/-- φ > 1, ensuring length1_10 = 1/φ < 1. -/
lemma phi_gt_one : φ > 1 := by
  unfold φ Real.goldenRatio
  have hsqrt : Real.sqrt 5 > 1 := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 5 := Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 5)
    have h2 : Real.sqrt 5 ≠ 1 := by
      intro heq
      have : (5 : ℝ) = 1 := by
        calc (5 : ℝ) = Real.sqrt 5 ^ 2 := (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)).symm
          _ = 1 ^ 2 := by rw [heq]
          _ = 1 := by norm_num
      norm_num at this
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  linarith

/-- The first interval length is positive. -/
lemma length1_10_pos : 0 < length1_10 := by
  unfold length1_10
  apply div_pos one_pos
  exact Real.goldenRatio_pos

/-- The second interval length is positive. -/
lemma length2_10_pos : 0 < length2_10 := by
  unfold length2_10
  have h := phi_gt_one
  have hφ_pos := Real.goldenRatio_pos
  have : 1 / φ < 1 := by
    rw [div_lt_one hφ_pos]
    exact h
  linarith

/-- The two interval lengths sum to 1. -/
lemma lengths_sum_to_one_10 : length1_10 + length2_10 = 1 := by
  unfold length1_10 length2_10
  ring

/-! ### Displacements -/

/-- The translation displacement for J₁: +0.382 = 2 - φ.

Points in [0, 1/φ) are translated forward by 2-φ, mapping them to [2-φ, 1). -/
noncomputable def displacement1_10 : ℝ := 2 - φ

/-- The translation displacement for J₂: -1/φ ≈ -0.618.

Points in [1/φ, 1) are translated backward by 1/φ, mapping them to [0, 2-φ). -/
noncomputable def displacement2_10 : ℝ := -(1 / φ)

/-- 2 - φ equals 1/φ². This is because φ² = φ + 1 implies 1/φ² = 1/(φ+1).
Then (2-φ)(φ+1) = 2φ + 2 - φ² - φ = φ + 2 - (φ+1) = 1. -/
lemma two_minus_phi_eq : 2 - φ = 1 / φ^2 := by
  have hφ_pos := Real.goldenRatio_pos
  have h := Real.goldenRatio_sq
  have hne : φ^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hφ_pos)
  rw [h]
  field_simp
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  linarith [hsq]

/-- 2 - φ is positive. -/
lemma two_minus_phi_pos : 0 < 2 - φ := by
  have h := phi_gt_one
  have h2 : φ < 2 := by
    unfold φ Real.goldenRatio
    have : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 3)]
      norm_num
    linarith
  linarith

/-- The displacements have the correct relationship: (2-φ) + 1/φ = 1.

Proof: Using φ² = φ + 1:
(2-φ) + 1/φ = ((2-φ)φ + 1)/φ = (2φ - φ² + 1)/φ = (2φ - (φ+1) + 1)/φ = φ/φ = 1 -/
lemma displacement_sum : displacement1_10 + length1_10 = 1 := by
  unfold displacement1_10 length1_10
  have hφ_pos := Real.goldenRatio_pos
  have h := Real.goldenRatio_sq
  have hne : φ ≠ 0 := ne_of_gt hφ_pos
  field_simp
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [hsq, sq_nonneg (Real.sqrt 5)]

/-! ### Generator Words -/

/-- The generator word w₁ = a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³ for interval J₁.

This depth-6 word maps points in J₁ = [0, 1/φ) to [2-φ, 1) by translation +0.382.

In Lean's Generator type:
- Generator.A is rotation by -2π/10 about (-1, 0)
- Generator.Ainv is rotation by +2π/10 about (-1, 0)
- Generator.B is rotation by -2π/10 about (1, 0)
- Generator.Binv is rotation by +2π/10 about (1, 0)

So a⁻⁴ means 4 applications of Ainv (i.e., rotation by +8π/10 = +4π/5 about left center). -/
def word1_10 : Word :=
  [Generator.Ainv, Generator.Ainv, Generator.Ainv, Generator.Ainv,  -- a⁻⁴
   Generator.Binv, Generator.Binv,                                  -- b⁻²
   Generator.Ainv, Generator.Ainv, Generator.Ainv, Generator.Ainv, Generator.Ainv, -- a⁻⁵
   Generator.Binv, Generator.Binv,                                  -- b⁻²
   Generator.Ainv, Generator.Ainv, Generator.Ainv, Generator.Ainv,  -- a⁻⁴
   Generator.Binv, Generator.Binv, Generator.Binv]                  -- b⁻³

/-- The generator word w₂ = a⁻¹b⁻¹ab for interval J₂.

This depth-4 word maps points in J₂ = [1/φ, 1) to [0, 2-φ) by translation -0.618. -/
def word2_10 : Word :=
  [Generator.Ainv,  -- a⁻¹
   Generator.Binv,  -- b⁻¹
   Generator.A,     -- a
   Generator.B]     -- b

/-! ### Permutation -/

/-- The swap permutation for 2 intervals: 0 ↔ 1.

Unlike GG5's cyclic permutation on 3 intervals, GG10's 2-interval IET uses a simple
swap. This is conjugate to rotation by 1/φ on the circle. -/
def swapPerm2 : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1

/-! ### The IET -/

/-- The 2-interval IET induced by the GG10 group action at critical radius.

At the critical radius r = √(4 - φ), the dynamics of GG10 on the invariant line
segment E'₁₀E₁₀ can be encoded as a 2-interval exchange transformation.

The two intervals have lengths 1/φ and 1-1/φ, and are swapped:
- J₁ = [0, 1/φ) maps to [1-1/φ, 1) via translation by 2-φ
- J₂ = [1/φ, 1) maps to [0, 1-1/φ) via translation by -1/φ

This is conjugate to irrational rotation by 1/φ, ensuring all orbits are infinite. -/
noncomputable def GG10_induced_IET : IntervalExchangeTransformation 2 where
  n_pos := by norm_num
  lengths := fun i => if i = 0 then length1_10 else length2_10
  lengths_pos := by
    intro i
    fin_cases i
    · simp only [show (0 : Fin 2) = 0 from rfl, ite_true]
      exact length1_10_pos
    · simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
      exact length2_10_pos
  lengths_sum := by
    have h_univ : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [h_univ]
    rw [Finset.sum_insert, Finset.sum_singleton]
    · simp only [show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false]
      exact lengths_sum_to_one_10
    · decide
  permutation := swapPerm2

/-! ### IET Word Function -/

/-- The generator word corresponding to a point's position in the IET partition.

Given a point x in [0,1), returns the word that encodes which interval x belongs to:
- If x < 1/φ: returns word1_10 (for interval J₁)
- Otherwise: returns word2_10 (for interval J₂) -/
noncomputable def IET_word_10 (x : ℝ) : Word :=
  if x < length1_10 then word1_10 else word2_10

/-- The concatenated word for k iterations of the IET starting at x0.

Builds the symbolic coding of the orbit by concatenating the words
corresponding to each visited interval. -/
noncomputable def wordForIterate_10 (x0 : ℝ) : ℕ → Word
  | 0 => []
  | n + 1 => wordForIterate_10 x0 n ++ IET_word_10 (GG10_induced_IET.toFun^[n] x0)

end TDCSG.GG10
