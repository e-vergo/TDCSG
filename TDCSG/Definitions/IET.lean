import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Real.GoldenRatio
import TDCSG.Definitions.WordCorrespondence

universe u

open Set

structure IntervalExchangeTransformation (n : ℕ) where

  n_pos : 0 < n

  lengths : Fin n → ℝ

  lengths_pos : ∀ i, 0 < lengths i

  lengths_sum : ∑ i, lengths i = 1

  permutation : Equiv.Perm (Fin n)

namespace IntervalExchangeTransformation

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

noncomputable def domainLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths ⟨j, Nat.lt_trans j.isLt i.isLt⟩

noncomputable def domainRight (i : Fin n) : ℝ :=
  iet.domainLeft i + iet.lengths i

noncomputable def rangeLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths (iet.permutation.symm ⟨j, Nat.lt_trans j.isLt i.isLt⟩)

noncomputable def rangeRight (i : Fin n) : ℝ :=
  iet.rangeLeft i + iet.lengths (iet.permutation i)

noncomputable def interval (i : Fin n) : Set ℝ :=
  Ico (iet.domainLeft i) (iet.domainRight i)

noncomputable def toFun : ℝ → ℝ := fun x =>
  Classical.epsilon fun y => ∃ i, x ∈ iet.interval i ∧
    y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)

end IntervalExchangeTransformation

section GeneralProperties

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

noncomputable def IET_inverse : IntervalExchangeTransformation n where
  n_pos := iet.n_pos
  lengths := fun i => iet.lengths (iet.permutation.symm i)
  lengths_pos := by intro i; exact iet.lengths_pos (iet.permutation.symm i)
  lengths_sum := by
    have : ∑ i, iet.lengths (iet.permutation.symm i) = ∑ i, iet.lengths i := by
      exact iet.permutation.symm.sum_comp iet.lengths
    rw [this]; exact iet.lengths_sum
  permutation := iet.permutation.symm

end GeneralProperties

namespace TDCSG.Definitions

open Real

noncomputable def length1 : ℝ :=
  1 / (2 * (1 + goldenRatio))

noncomputable def length2 : ℝ :=
  1 / (2 * (1 + goldenRatio))

noncomputable def length3 : ℝ :=
  1 / goldenRatio

noncomputable def displacement0 : ℝ := length3

noncomputable def displacement1 : ℝ := length3

noncomputable def displacement2 : ℝ := -(length1 + length2)

private lemma one_plus_phi_pos : 0 < 1 + Real.goldenRatio := by
  have h1 : 0 < Real.goldenRatio := Real.goldenRatio_pos
  linarith

lemma length1_pos : 0 < length1 := by
  unfold length1
  exact div_pos one_pos (by linarith [one_plus_phi_pos])

lemma length2_pos : 0 < length2 := by
  unfold length2
  exact div_pos one_pos (by linarith [one_plus_phi_pos])

lemma length3_pos : 0 < length3 := by
  unfold length3
  exact div_pos one_pos Real.goldenRatio_pos

lemma lengths_sum_to_one : length1 + length2 + length3 = 1 := by
  unfold length1 length2 length3
  have h_phi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have h_one_plus_phi_pos : 0 < 1 + Real.goldenRatio := one_plus_phi_pos
  have h_phi_ne : Real.goldenRatio ≠ 0 := ne_of_gt h_phi_pos
  have h_one_plus_phi_ne : 1 + Real.goldenRatio ≠ 0 := ne_of_gt h_one_plus_phi_pos
  have h_two_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_sq := Real.goldenRatio_sq
  have h_key : Real.goldenRatio * (1 + Real.goldenRatio) = 1 + 2 * Real.goldenRatio := by
    calc Real.goldenRatio * (1 + Real.goldenRatio)
        = Real.goldenRatio + Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio + (Real.goldenRatio + 1) := by rw [h_sq]
      _ = 1 + 2 * Real.goldenRatio := by ring
  have h_sum : Real.goldenRatio + (1 + Real.goldenRatio) = 1 + 2 * Real.goldenRatio := by ring
  have h_prod_pos : 0 < Real.goldenRatio * (1 + Real.goldenRatio) := by positivity
  have h_prod_ne : Real.goldenRatio * (1 + Real.goldenRatio) ≠ 0 := ne_of_gt h_prod_pos
  calc 1 / (2 * (1 + Real.goldenRatio)) + 1 / (2 * (1 + Real.goldenRatio)) + 1 / Real.goldenRatio
      = 2 / (2 * (1 + Real.goldenRatio)) + 1 / Real.goldenRatio := by ring
    _ = 1 / (1 + Real.goldenRatio) + 1 / Real.goldenRatio := by
        congr 1; field_simp
    _ = (Real.goldenRatio + (1 + Real.goldenRatio)) / (Real.goldenRatio * (1 + Real.goldenRatio)) := by
        field_simp
    _ = (1 + 2 * Real.goldenRatio) / (Real.goldenRatio * (1 + Real.goldenRatio)) := by rw [h_sum]
    _ = (1 + 2 * Real.goldenRatio) / (1 + 2 * Real.goldenRatio) := by rw [h_key]
    _ = 1 := by field_simp

def cyclicPerm3 : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2

noncomputable def GG5_induced_IET : IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i =>
    if i = 0 then length1
    else if i = 1 then length2
    else length3
  lengths_pos := by
    intro i
    fin_cases i
    all_goals simp only
    · exact length1_pos
    · exact length2_pos
    · exact length3_pos
  lengths_sum := by
    have h_univ : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [h_univ]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [show (1 : Fin 3) = 0 ↔ False by decide,
                 show (2 : Fin 3) = 0 ↔ False by decide,
                 show (2 : Fin 3) = 1 ↔ False by decide,
                 ite_true, ite_false]
      have h := lengths_sum_to_one
      ring_nf at h ⊢
      exact h
    · decide
    · decide
  permutation := cyclicPerm3

open TDCSG.CompoundSymmetry.GG5

noncomputable def IET_word (x : Real) : Word :=
  if x < length1 then word1
  else if x < length1 + length2 then word2
  else word3

noncomputable def wordForIterate (x0 : Real) : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate x0 n ++ IET_word (GG5_induced_IET.toFun^[n] x0)

noncomputable def wordForIterate' : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate' n ++ word1

end TDCSG.Definitions
