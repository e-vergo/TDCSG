/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.IET
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interval Exchange Transformation Proofs

This file contains proofs about interval exchange transformations (IETs)
and the specific GG5-induced IET.

## Main results

### General IET properties
- `intervals_cover`: The union of all intervals is [0, 1)
- `intervals_disjoint`: Intervals are pairwise disjoint
- `interval_injective`: The interval function is injective
- `domainLeft_strictMono`: Left endpoints are strictly monotone
- `domainRight_le_domainLeft_of_lt`: Contiguity of intervals

### GG5 IET
- `GG5_induced_IET`: 3-interval exchange transformation induced by GG(5,5) dynamics
- Golden ratio displacement formulas

-/

/-! ### General IET properties -/

namespace IntervalExchangeTransformation

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

open Set

/-- Basic property: domain intervals are nonempty. -/
theorem interval_nonempty (i : Fin n) : (iet.interval i).Nonempty := by
  use iet.domainLeft i
  simp only [interval, mem_Ico]
  constructor
  · rfl
  · simp only [domainRight]
    linarith [iet.lengths_pos i]

/-- The union of all intervals is [0, 1). -/
theorem intervals_cover : ⋃ i, iet.interval i = Ico 0 1 := by
  ext x
  simp only [Set.mem_iUnion, interval, mem_Ico]
  constructor
  · -- If x is in some interval, then 0 <= x < 1
    intro ⟨i, hx⟩
    constructor
    · -- x >= 0: follows from domainLeft i >= 0
      calc x ≥ iet.domainLeft i := hx.1
        _ ≥ 0 := by
          unfold domainLeft
          apply Finset.sum_nonneg
          intro j _
          exact le_of_lt (iet.lengths_pos _)
    · -- x < 1: follows from domainRight i <= 1 and sum of all lengths = 1
      have h_right_le : iet.domainRight i ≤ 1 := by
        calc iet.domainRight i
          _ = iet.domainLeft i + iet.lengths i := rfl
          _ ≤ ∑ j : Fin n, iet.lengths j := by
            rw [domainLeft]
            have h_le : i.val.succ ≤ n := i.isLt
            calc ∑ j : Fin i.val, iet.lengths ⟨j, Nat.lt_trans j.isLt i.isLt⟩ + iet.lengths i
              _ = ∑ j : Fin i.val.succ, iet.lengths ⟨j, Nat.lt_of_lt_of_le j.isLt h_le⟩ := by
                rw [Fin.sum_univ_castSucc]
                congr 1
              _ ≤ ∑ j : Fin n, iet.lengths j := by
                have h_image : Finset.univ.image (Fin.castLE h_le) ⊆ Finset.univ := by
                  simp only [Finset.subset_univ]
                calc ∑ j : Fin i.val.succ, iet.lengths ⟨j, Nat.lt_of_lt_of_le j.isLt h_le⟩
                    = ∑ j : Fin i.val.succ, iet.lengths (Fin.castLE h_le j) := by
                      rfl
                  _ = ∑ j ∈ Finset.univ.image (Fin.castLE h_le), iet.lengths j := by
                      rw [Finset.sum_image]
                      intro _ _ _ _ h
                      exact Fin.castLE_injective h_le h
                  _ ≤ ∑ j : Fin n, iet.lengths j := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg h_image
                      intro j _ _
                      exact le_of_lt (iet.lengths_pos j)
          _ = 1 := iet.lengths_sum
      calc x < iet.domainRight i := hx.2
        _ ≤ 1 := h_right_le
  · -- If 0 <= x < 1, then x is in some interval
    intro ⟨hx0, hx1⟩
    have h_left_0 : iet.domainLeft ⟨0, iet.n_pos⟩ = 0 := by
      unfold domainLeft
      simp

    have h_minimal_exists : ∃ i : Fin n, x < iet.domainRight i ∧
        ∀ j : Fin n, j < i → iet.domainRight j ≤ x := by
      have h_exists_some : ∃ i : Fin n, x < iet.domainRight i := by
        have h_n_minus_1_lt : n - 1 < n := Nat.pred_lt (Nat.pos_iff_ne_zero.mp iet.n_pos)
        have h_last : iet.domainRight ⟨n - 1, h_n_minus_1_lt⟩ = 1 := by
          unfold domainRight domainLeft
          rw [← iet.lengths_sum]
          have h_sum_eq : ∑ j : Fin (n - 1), iet.lengths ⟨↑j, Nat.lt_trans j.isLt h_n_minus_1_lt⟩ =
                          ∑ j : Fin (n - 1), iet.lengths ⟨j.val, by omega⟩ := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1

          rw [h_sum_eq]
          clear h_sum_eq

          have h_partition : (Finset.univ : Finset (Fin n)) =
                             (Finset.univ.image (fun j : Fin (n-1) => (⟨j.val, by omega⟩ : Fin n))) ∪
                             {⟨n-1, h_n_minus_1_lt⟩} := by
            ext i
            simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, Finset.mem_singleton, true_iff]
            by_cases hi : i.val < n - 1
            · left
              use ⟨i.val, hi⟩
            · right
              push_neg at hi
              have : i.val = n - 1 := by omega
              ext; exact this

          rw [h_partition, Finset.sum_union, Finset.sum_singleton]
          · congr 1
            rw [Finset.sum_image]
            intro x1 _ x2 _ h
            exact Fin.ext (Fin.mk_eq_mk.mp h)
          · simp only [Finset.disjoint_singleton_right, Finset.mem_image, not_exists, not_and]
            intro j _ h
            have : j.val = n - 1 := Fin.mk_eq_mk.mp h
            omega
        use ⟨n - 1, h_n_minus_1_lt⟩
        rw [h_last]
        exact hx1
      let S : Finset (Fin n) := Finset.univ.filter (fun i => x < iet.domainRight i)

      have hS_nonempty : S.Nonempty := by
        obtain ⟨i, hi⟩ := h_exists_some
        use i
        simp [S]
        exact hi

      let i_min := S.min' hS_nonempty

      have hi_min_mem : i_min ∈ S := Finset.min'_mem S hS_nonempty
      have hi_min_upper : x < iet.domainRight i_min := by
        simp [S] at hi_min_mem
        exact hi_min_mem

      have hi_minimal : ∀ j, j < i_min → iet.domainRight j ≤ x := by
        intro j hj
        by_contra h_contra
        push_neg at h_contra
        have : j ∈ S := by
          simp [S]
          exact h_contra
        have : i_min ≤ j := Finset.min'_le S j this
        omega

      use i_min, hi_min_upper, hi_minimal

    obtain ⟨i, hi_upper, hi_minimal⟩ := h_minimal_exists

    have hi_lower : iet.domainLeft i ≤ x := by
      by_cases h_i_zero : i.val = 0
      · have : i = ⟨0, by omega⟩ := Fin.ext h_i_zero
        rw [this, h_left_0]
        exact hx0
      · have h_i_pos : 0 < i.val := by omega
        have h_pred_lt : i.val - 1 < n := by omega
        let i_pred : Fin n := ⟨i.val - 1, h_pred_lt⟩

        have h_pred_lt_i : i_pred < i := by
          show i.val - 1 < i.val
          omega

        have h_succ : i_pred.val + 1 = i.val := by
          simp [i_pred]
          omega

        have h_i_succ_lt : i_pred.val + 1 < n := by
          simp [i_pred]
          omega

        have h_contiguity : iet.domainRight i_pred = iet.domainLeft i := by
          unfold domainRight domainLeft
          have h_i_as_succ : ∃ h, i = ⟨i_pred.val + 1, h⟩ := by
            use h_i_succ_lt
            ext
            simp [i_pred]
            omega
          obtain ⟨h_i_bound, h_i_eq⟩ := h_i_as_succ
          rw [h_i_eq]
          simp only
          rw [Fin.sum_univ_castSucc]
          congr 1

        have h_min_bound : iet.domainRight i_pred ≤ x := hi_minimal i_pred h_pred_lt_i

        calc iet.domainLeft i
            = iet.domainRight i_pred := h_contiguity.symm
          _ ≤ x := h_min_bound

    use i

/-- domainLeft is strictly monotone increasing. -/
lemma domainLeft_strictMono {i j : Fin n} (hij : i < j) : iet.domainLeft i < iet.domainLeft j := by
  unfold domainLeft
  have h_i_lt_n : i.val < n := i.isLt
  have h_j_lt_n : j.val < n := j.isLt
  have h_ival_lt_jval : i.val < j.val := hij
  have h_succ_le : i.val.succ ≤ j.val := h_ival_lt_jval
  calc ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_i_lt_n⟩
      < ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_i_lt_n⟩ + iet.lengths ⟨i.val, Nat.lt_trans h_ival_lt_jval h_j_lt_n⟩ := by
        linarith [iet.lengths_pos ⟨i.val, Nat.lt_trans h_ival_lt_jval h_j_lt_n⟩]
    _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_j_lt_n⟩ := by
        calc ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_i_lt_n⟩ + iet.lengths ⟨i.val, Nat.lt_trans h_ival_lt_jval h_j_lt_n⟩
            = ∑ k : Fin i.val.succ, iet.lengths ⟨k, Nat.lt_of_lt_of_le k.isLt (Nat.le_trans h_succ_le (Nat.le_of_lt h_j_lt_n))⟩ := by
              rw [Fin.sum_univ_castSucc]
              congr 1
          _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_j_lt_n⟩ := by
              have h_le_jval : i.val.succ ≤ j.val := h_succ_le
              have h_image : Finset.univ.image (Fin.castLE h_le_jval) ⊆ Finset.univ := by
                simp only [Finset.subset_univ]
              calc ∑ k : Fin i.val.succ, iet.lengths ⟨k, Nat.lt_of_lt_of_le k.isLt (Nat.le_trans h_succ_le (Nat.le_of_lt h_j_lt_n))⟩
                  = ∑ k : Fin i.val.succ, iet.lengths ⟨(Fin.castLE h_le_jval k).val, Nat.lt_trans (Fin.castLE h_le_jval k).isLt h_j_lt_n⟩ := by
                    congr 1
                _ = ∑ k ∈ Finset.univ.image (Fin.castLE h_le_jval), iet.lengths ⟨k.val, Nat.lt_trans k.isLt h_j_lt_n⟩ := by
                    rw [Finset.sum_image]
                    intro _ _ _ _ h
                    exact Fin.castLE_injective h_le_jval h
                _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_j_lt_n⟩ := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg h_image
                    intro k _ _
                    exact le_of_lt (iet.lengths_pos ⟨k, Nat.lt_trans k.isLt h_j_lt_n⟩)

/-- domainLeft is monotone increasing. -/
lemma domainLeft_mono {i j : Fin n} (hij : i ≤ j) : iet.domainLeft i ≤ iet.domainLeft j := by
  unfold domainLeft
  by_cases h_eq : i = j
  · rw [h_eq]
  · have hij_strict : i.val < j.val := Nat.lt_of_le_of_ne hij (fun h => h_eq (Fin.eq_of_val_eq h))
    have h_le : i.val ≤ j.val := hij
    have h_image_subset : Finset.univ.image (Fin.castLE h_le) ⊆ (Finset.univ : Finset (Fin j.val)) := by
      intro x hx
      simp only [Finset.mem_univ]
    calc ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt i.isLt⟩
        = ∑ k : Fin i.val, iet.lengths ⟨(Fin.castLE h_le k).val, Nat.lt_trans (Fin.castLE h_le k).isLt j.isLt⟩ := by
          congr 1
      _ = ∑ k ∈ Finset.univ.image (Fin.castLE h_le), iet.lengths ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ := by
          rw [Finset.sum_image]
          intro _ _ _ _ h
          exact Fin.castLE_injective h_le h
      _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt j.isLt⟩ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_image_subset
          intro k _ _
          exact le_of_lt (iet.lengths_pos ⟨k, Nat.lt_trans k.isLt j.isLt⟩)

/-- Intervals are contiguous: the right endpoint of interval i equals the left endpoint of interval i+1. -/
lemma domainRight_eq_domainLeft_succ (i : Fin n) (hi : i.val + 1 < n) :
    iet.domainRight i = iet.domainLeft ⟨i.val + 1, hi⟩ := by
  unfold domainRight domainLeft
  rw [Fin.sum_univ_castSucc]
  congr 1

/-- Helper lemma: domainRight i <= domainLeft j when i < j. -/
lemma domainRight_le_domainLeft_of_lt {i j : Fin n} (hij : i < j) :
    iet.domainRight i ≤ iet.domainLeft j := by
  unfold domainRight domainLeft
  by_cases h_succ_eq : i.val.succ = j.val
  · have h_cons : i.val + 1 < n := by
      calc i.val + 1 = j.val := h_succ_eq
        _ < n := j.isLt
    have : ⟨i.val.succ, h_cons⟩ = j := by
      ext
      simp [Nat.succ_eq_add_one]
      exact h_succ_eq
    rw [← this]
    exact le_of_eq (iet.domainRight_eq_domainLeft_succ i h_cons)
  · have h_succ_lt : i.val.succ < j.val := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hij) h_succ_eq
    have h_cons : i.val + 1 < n := Nat.lt_trans h_succ_lt j.isLt
    have h_le : ⟨i.val + 1, h_cons⟩ ≤ j := by
      show (⟨i.val + 1, h_cons⟩ : Fin n).val ≤ j.val
      exact Nat.le_of_lt h_succ_lt
    calc iet.domainRight i
        = iet.domainLeft ⟨i.val + 1, h_cons⟩ := iet.domainRight_eq_domainLeft_succ i h_cons
      _ ≤ iet.domainLeft j := iet.domainLeft_mono h_le

/-- The intervals are pairwise disjoint. -/
theorem intervals_disjoint : (Set.range iet.interval).PairwiseDisjoint (fun x => x) := by
  intro s hs t ht hst
  obtain ⟨i, rfl⟩ := hs
  obtain ⟨j, rfl⟩ := ht
  unfold interval
  by_cases hij : i < j
  · apply Set.disjoint_iff_inter_eq_empty.mpr
    ext x
    simp only [Set.mem_inter_iff, mem_Ico, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx₁ hx₂
    have h_le := iet.domainRight_le_domainLeft_of_lt hij
    linarith
  · by_cases hji : j < i
    · apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, mem_Ico, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx₁ hx₂
      have h_le := iet.domainRight_le_domainLeft_of_lt hji
      linarith
    · push_neg at hij hji
      have heq : i = j := Fin.eq_of_val_eq (Nat.le_antisymm hji hij)
      rw [heq] at hst
      exact absurd rfl hst

/-- The interval function is injective. -/
lemma interval_injective : Function.Injective (interval iet) := by
  intro i j h_eq
  unfold interval at h_eq
  by_cases hij : i < j
  · have h_left_lt : iet.domainLeft i < iet.domainLeft j := iet.domainLeft_strictMono hij
    have h_left_eq : iet.domainLeft i = iet.domainLeft j := by
      have h_i_mem : iet.domainLeft i ∈ Ico (iet.domainLeft i) (iet.domainRight i) := by
        rw [mem_Ico]
        constructor
        · rfl
        · simp only [domainRight]
          linarith [iet.lengths_pos i]
      rw [h_eq] at h_i_mem
      rw [mem_Ico] at h_i_mem
      have h_j_le_i : iet.domainLeft j ≤ iet.domainLeft i := h_i_mem.1
      have h_j_mem : iet.domainLeft j ∈ Ico (iet.domainLeft j) (iet.domainRight j) := by
        rw [mem_Ico]
        constructor
        · rfl
        · simp only [domainRight]
          linarith [iet.lengths_pos j]
      rw [← h_eq] at h_j_mem
      rw [mem_Ico] at h_j_mem
      have h_i_le_j : iet.domainLeft i ≤ iet.domainLeft j := h_j_mem.1
      exact le_antisymm h_i_le_j h_j_le_i
    linarith
  · by_cases hji : j < i
    · have h_left_lt : iet.domainLeft j < iet.domainLeft i := iet.domainLeft_strictMono hji
      have h_left_eq : iet.domainLeft i = iet.domainLeft j := by
        have h_i_mem : iet.domainLeft i ∈ Ico (iet.domainLeft i) (iet.domainRight i) := by
          rw [mem_Ico]
          constructor
          · rfl
          · simp only [domainRight]
            linarith [iet.lengths_pos i]
        rw [h_eq] at h_i_mem
        rw [mem_Ico] at h_i_mem
        have h_j_le_i : iet.domainLeft j ≤ iet.domainLeft i := h_i_mem.1
        have h_j_mem : iet.domainLeft j ∈ Ico (iet.domainLeft j) (iet.domainRight j) := by
          rw [mem_Ico]
          constructor
          · rfl
          · simp only [domainRight]
            linarith [iet.lengths_pos j]
        rw [← h_eq] at h_j_mem
        rw [mem_Ico] at h_j_mem
        have h_i_le_j : iet.domainLeft i ≤ iet.domainLeft j := h_j_mem.1
        exact le_antisymm h_i_le_j h_j_le_i
      linarith
    · push_neg at hij hji
      exact Fin.eq_of_val_eq (Nat.le_antisymm hji hij)

end IntervalExchangeTransformation

/-! ### GG5 IET Proofs -/

namespace TDCSG.CompoundSymmetry.GG5

open Real TDCSG.Definitions

-- Re-export definitions from TDCSG.Definitions for backward compatibility
-- These are now defined in Definitions/IET.lean
export TDCSG.Definitions (cyclicPerm3 GG5_induced_IET
  length1_pos length2_pos length3_pos lengths_sum_to_one)

/-- 1 + φ is positive. -/
private lemma one_plus_phi_pos : 0 < 1 + goldenRatio := by
  have h1 : 0 < goldenRatio := goldenRatio_pos
  linarith

/-- length1 < 1 -/
lemma length1_lt_one : length1 < 1 := by
  have h := lengths_sum_to_one
  linarith [length2_pos, length3_pos]

/-- length1 + length2 < 1 -/
lemma length12_lt_one : length1 + length2 < 1 := by
  have h := lengths_sum_to_one
  linarith [length3_pos]

/-- The interval lengths satisfy: length1 = length2 (equal short segments). -/
theorem length1_eq_length2 : length1 = length2 := rfl

/-- length3 = 1/φ = ψ (the golden conjugate, positive version). -/
theorem length3_eq_one_over_phi : length3 = 1 / goldenRatio := rfl

/-- length1 + length2 = ψ² = 1 - ψ (using ψ + ψ² = 1). -/
lemma length12_sum : length1 + length2 = 1 / (1 + goldenRatio) := by
  unfold length1 length2
  have h_pos : 0 < 1 + goldenRatio := one_plus_phi_pos
  have h_ne : 2 * (1 + goldenRatio) ≠ 0 := by linarith
  field_simp; norm_num

/-! ### Displacement formulas in terms of golden ratio -/

/-- Displacement 0 formula: d₀ = length3 = 1/φ = ψ ≈ 0.618. -/
lemma displacement0_formula : displacement0 = 1 / goldenRatio := by
  unfold displacement0 length3
  rfl

/-- Displacement 1 formula: d₁ = length3 = 1/φ = ψ ≈ 0.618.
    Same as displacement0 since both intervals shift by the same amount. -/
lemma displacement1_formula : displacement1 = 1 / goldenRatio := by
  unfold displacement1 length3
  rfl

/-- Displacement 2 formula: d₂ = -(length1 + length2) = -1/(1+φ) = -ψ² ≈ -0.382. -/
lemma displacement2_formula : displacement2 = -1 / (1 + goldenRatio) := by
  unfold displacement2 length1 length2
  have h_pos : 0 < 1 + goldenRatio := one_plus_phi_pos
  have h_ne : 2 * (1 + goldenRatio) ≠ 0 := by linarith
  have h_ne' : (1 + goldenRatio) ≠ 0 := by linarith
  calc -(1 / (2 * (1 + goldenRatio)) + 1 / (2 * (1 + goldenRatio)))
      = -(2 / (2 * (1 + goldenRatio))) := by ring
    _ = -(1 / (1 + goldenRatio)) := by field_simp
    _ = -1 / (1 + goldenRatio) := by ring

/-- displacement0 = displacement1 (both equal ψ). -/
lemma displacement0_eq_displacement1 : displacement0 = displacement1 := by
  rw [displacement0_formula, displacement1_formula]

/-- displacement2 = -(length1 + length2) = -ψ². -/
lemma displacement2_eq_neg_length12 : displacement2 = -(length1 + length2) := rfl

end TDCSG.CompoundSymmetry.GG5
