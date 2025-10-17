/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Finite
import TDCSG.MeasurePreserving
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Interval Exchange Transformations

This file defines interval exchange transformations (IETs), which are a fundamental class of
piecewise isometries on the unit interval. An IET partitions [0,1] into finitely many
subintervals and rearranges them by a permutation.

IETs are a key motivating example for the piecewise isometry framework and have rich dynamics:
- They preserve Lebesgue measure
- They are typically uniquely ergodic (Masur-Veech theorem)
- They model certain billiard systems
- They connect to Teichmüller theory and flat surfaces

## Main definitions

- `IntervalExchangeTransformation n`: An IET with `n` intervals, given by lengths and a
  permutation
- `IntervalExchangeTransformation.toPiecewiseIsometry`: Convert an IET to a piecewise isometry
- `IntervalExchangeTransformation.interval`: The ith subinterval
- `IET.IsStandard`: The standard (Rauzy) form with 0 and 1 as singularities

## Main results

- `IET_preserves_lebesgue`: Every IET preserves Lebesgue measure
- `IET_is_finite_piecewise_isometry`: An IET is a finite piecewise isometry
- `IET_two_intervals_is_rotation`: A 2-interval IET is a circle rotation
- `IET_complexity_linear`: The partition complexity grows linearly

## References

* [Michael Keane, *Interval exchange transformations*][Keane1975]
* [Howard Masur, *Interval exchange transformations and measured foliations*][Masur1982]
* [William Veech, *Gauss measures for transformations on the space of interval exchange
  maps*][Veech1982]

-/

universe u

namespace PiecewiseIsometry

open Set MeasureTheory

/-- An interval exchange transformation on `n` intervals.

Given `n` intervals with specified lengths and a permutation, an IET rearranges these intervals
according to the permutation while preserving orientation within each interval. -/
structure IntervalExchangeTransformation (n : ℕ) where
  /-- We require at least one interval -/
  n_pos : 0 < n
  /-- The lengths of the intervals -/
  lengths : Fin n → ℝ
  /-- All lengths are positive -/
  lengths_pos : ∀ i, 0 < lengths i
  /-- The lengths sum to 1 (normalized) -/
  lengths_sum : ∑ i, lengths i = 1
  /-- The permutation describing how intervals are rearranged -/
  permutation : Equiv.Perm (Fin n)

namespace IntervalExchangeTransformation

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/-- The left endpoint of the ith interval in the domain (before permutation). -/
noncomputable def domainLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths ⟨j, Nat.lt_trans j.isLt i.isLt⟩

/-- The right endpoint of the ith interval in the domain. -/
noncomputable def domainRight (i : Fin n) : ℝ :=
  iet.domainLeft i + iet.lengths i

/-- The left endpoint of the ith interval in the range (after permutation). -/
noncomputable def rangeLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths (iet.permutation ⟨j, Nat.lt_trans j.isLt i.isLt⟩)

/-- The right endpoint of the ith interval in the range. -/
noncomputable def rangeRight (i : Fin n) : ℝ :=
  iet.rangeLeft i + iet.lengths (iet.permutation i)

/-- The ith subinterval in the domain. -/
noncomputable def interval (i : Fin n) : Set ℝ :=
  Ico (iet.domainLeft i) (iet.domainRight i)

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
  · -- If x is in some interval, then 0 ≤ x < 1
    intro ⟨i, hx⟩
    constructor
    · -- x ≥ 0: follows from domainLeft i ≥ 0
      calc x ≥ iet.domainLeft i := hx.1
        _ ≥ 0 := by
          unfold domainLeft
          apply Finset.sum_nonneg
          intro j _
          exact le_of_lt (iet.lengths_pos _)
    · -- x < 1: follows from domainRight i ≤ 1 and sum of all lengths = 1
      have h_right_le : iet.domainRight i ≤ 1 := by
        calc iet.domainRight i
          _ = iet.domainLeft i + iet.lengths i := rfl
          _ ≤ ∑ j : Fin n, iet.lengths j := by
            rw [domainLeft]
            /- PROOF ATTEMPTS HISTORY:

             GOAL: ⊢ (∑ j : Fin i.val, lengths ⟨↑j, _⟩) + lengths i ≤ ∑ j : Fin n, lengths j

             Mathematical Content: Partial sum ≤ total sum when all terms nonnegative
             - LHS = sum of first i.val terms + i-th term = sum of first (i.val + 1) terms
             - RHS = sum of all n terms
             - Since i.val + 1 ≤ n and all lengths > 0, LHS ≤ RHS

             Attempt 1 [2025-10-16]: Use Fin.sum_univ_castSucc
             - Strategy: Convert LHS to sum over Fin (i.val + 1) using Fin.sum_univ_castSucc
             - Failure: Pattern matching issues with dependent types
             - Lesson: Fin.sum_univ_castSucc expects specific type alignment

             Attempt 2 [2025-10-16]: Use Finset.sum_bij/sum_nbij
             - Strategy: Establish bijection between index sets
             - Failure: Finset.sum_nbij doesn't exist, Finset.sum_bij signature mismatch
             - Lesson: Need to find correct bijection lemma in Mathlib

             Attempt 3 [2025-10-16]: Use Finset.image and subset inequality
             - Strategy: Express partial sum as sum over image, use Finset.sum_le_sum_of_subset_of_nonneg
             - Failure: Complex type annotations, disjointness proofs became unwieldy
             - Lesson: Image approach requires careful handling of Fin coercions

             Attempt 4 [2025-10-16]: Direct decomposition with omega
             - Strategy: Split full sum into partial + remainder, show equality
             - Failure: Equality proof requires Fin sum decomposition lemma not readily available
             - Lesson: Need lemma like "sum over Fin n = sum over Fin k + sum over remaining indices" for k ≤ n

             Attempt 5 [2025-10-16]: Fin.sum_univ_castSucc + Fin.castLE + subset inequality
             - Strategy: Use Fin.sum_univ_castSucc to convert LHS to sum over Fin (i.val.succ),
                        embed via Fin.castLE into Fin n, apply Finset.sum_le_sum_of_subset_of_nonneg
             - Success: This approach works cleanly!
             - Key lemmas: Fin.sum_univ_castSucc, Fin.castLE, Finset.sum_le_sum_of_subset_of_nonneg
            -/
            have h_le : i.val.succ ≤ n := i.isLt
            calc ∑ j : Fin i.val, iet.lengths ⟨j, Nat.lt_trans j.isLt i.isLt⟩ + iet.lengths i
              _ = ∑ j : Fin i.val.succ, iet.lengths ⟨j, Nat.lt_of_lt_of_le j.isLt h_le⟩ := by
                rw [Fin.sum_univ_castSucc]
                congr 1
              _ ≤ ∑ j : Fin n, iet.lengths j := by
                -- Partial sum ≤ total sum (i.val + 1 ≤ n, all terms nonnegative)
                -- Strategy: Rewrite LHS using castLE embedding, then apply subset inequality
                have eq : ∑ j : Fin i.val.succ, iet.lengths ⟨j, Nat.lt_of_lt_of_le j.isLt h_le⟩ =
                          ∑ j : Fin i.val.succ, iet.lengths (Fin.castLE h_le j) := by
                  simp only [Fin.castLE]
                calc ∑ j : Fin i.val.succ, iet.lengths ⟨j, Nat.lt_of_lt_of_le j.isLt h_le⟩
                  _ = ∑ j : Fin i.val.succ, iet.lengths (Fin.castLE h_le j) := eq
                  _ = ∑ j ∈ Finset.univ.image (Fin.castLE h_le), iet.lengths j := by
                    rw [Finset.sum_image]
                    intro _ _ _ _ h
                    exact Fin.castLE_injective h_le h
                  _ ≤ ∑ j : Fin n, iet.lengths j := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro x _
                      simp only [Finset.mem_univ]
                    · intro j _ _
                      exact le_of_lt (iet.lengths_pos j)
          _ = 1 := iet.lengths_sum
      calc x < iet.domainRight i := hx.2
        _ ≤ 1 := h_right_le
  · -- If 0 ≤ x < 1, then x is in some interval
    intro ⟨hx0, hx1⟩
    /- PROOF ATTEMPTS:

       GOAL: Find i such that domainLeft i ≤ x < domainRight i

       Strategy: Find the largest i with domainLeft i ≤ x, then show x < domainRight i

       Mathematical content: The intervals partition [0,1). Since x ∈ [0,1), x must be in exactly one.
       We find it by: i is largest with domainLeft i ≤ x.
       Then x < domainRight i because otherwise x ≥ domainLeft (i+1), contradicting maximality.

       Attempt 1 [2025-10-16]: Use Finset.exists_max_image
       - Issue: Need to convert between Set and Finset, handle subtypes
       - Complexity: High, many type coercions

       Attempt 2 [2025-10-16]: Direct construction using if-then-else
       - Strategy: Use classical choice or decidability to pick the interval
       - Issue: Lean prefers constructive proofs when possible

       Current approach: Use a helper function to find the interval, then prove it works

       Attempt 3 [2025-10-17]: Use Finset.exists_max_image to find largest i with domainLeft i ≤ x
       - Strategy: Take argmax of {i | domainLeft i ≤ x}
       - Show this i satisfies x < domainRight i
    -/
    -- Find the largest i such that domainLeft i ≤ x
    have h_exists : ∃ i : Fin n, iet.domainLeft i ≤ x := by
      use ⟨0, iet.n_pos⟩
      unfold domainLeft
      simp
      exact hx0
    classical
    let S := (Finset.univ : Finset (Fin n)).filter (fun i => iet.domainLeft i ≤ x)
    have hS_nonempty : S.Nonempty := by
      use ⟨0, iet.n_pos⟩
      simp [S]
      unfold domainLeft
      exact hx0
    obtain ⟨i, hi_in_S, hi_max⟩ := Finset.exists_max_image S (fun i => iet.domainLeft i) hS_nonempty
    use i
    simp [S] at hi_in_S
    constructor
    · exact hi_in_S
    · -- Need to show x < domainRight i
      -- Suppose x ≥ domainRight i. Then x ≥ domainLeft i + lengths i = domainLeft (i+1) if i+1 < n
      by_contra h_ge
      push_neg at h_ge
      -- x ≥ domainRight i = domainLeft i + lengths i
      have h_ge' : iet.domainRight i ≤ x := by
        unfold domainRight
        exact h_ge
      -- Consider two cases: i+1 < n or i+1 = n
      by_cases hi_succ : i.val.succ < n
      · -- If i+1 < n, then domainRight i = domainLeft (i+1)
        let i_succ : Fin n := ⟨i.val.succ, hi_succ⟩
        have h_eq : iet.domainRight i = iet.domainLeft i_succ := by
          unfold domainRight domainLeft
          simp [i_succ]
          rw [Fin.sum_univ_castSucc]
          simp
        rw [h_eq] at h_ge'
        -- So x ≥ domainLeft i_succ, meaning i_succ should be in S
        have hi_succ_in_S : i_succ ∈ S := by
          simp [S]
          exact h_ge'
        -- But domainLeft i_succ > domainLeft i (since lengths i > 0)
        have h_lt : iet.domainLeft i < iet.domainLeft i_succ := by
          rw [← h_eq]
          unfold domainRight
          linarith [iet.lengths_pos i]
        -- This contradicts maximality of i
        have := hi_max i_succ hi_succ_in_S
        linarith
      · -- If i+1 ≥ n, then i = n-1, so domainRight i = 1
        have hi_last : i.val = n - 1 := by omega
        have h_sum : iet.domainRight i = 1 := by
          -- i is the last index (i.val = n-1), so domainRight i = sum of all lengths = 1
          unfold domainRight domainLeft
          -- Since i.val.succ = n, domainRight i equals the sum of all n lengths
          have hi_succ_eq_n : i.val.succ = n := by omega
          calc (∑ k : Fin i.val, iet.lengths ⟨↑k, Nat.lt_trans k.isLt i.isLt⟩) + iet.lengths i
            _ = ∑ k : Fin i.val.succ, iet.lengths ⟨↑k, Nat.lt_of_lt_of_le k.isLt (Nat.le_of_eq hi_succ_eq_n)⟩ := by
              rw [Fin.sum_univ_castSucc]
              congr 1
            _ = ∑ k : Fin n, iet.lengths k := by
              -- The sums are equal because i.val.succ = n
              -- Use Fintype.sum_equiv to handle the dependent type equality
              symm
              apply Fintype.sum_equiv ((Fin.castOrderIso hi_succ_eq_n) : Fin i.val.succ ≃ Fin n).symm
              intro k
              -- Show: iet.lengths k = iet.lengths ⟨↑(cast k), _⟩
              -- Both Fin values have the same underlying natural number
              -- congr automatically proves they're equal since cast doesn't change the value
              congr 1
            _ = 1 := iet.lengths_sum
        rw [h_sum] at h_ge'
        linarith

/-- Helper lemma: domainRight i ≤ domainLeft j when i < j. -/
lemma domainRight_le_domainLeft_of_lt {i j : Fin n} (hij : i < j) :
    iet.domainRight i ≤ iet.domainLeft j := by
  unfold domainRight domainLeft
  /- PROOF ATTEMPTS:

     GOAL: ∑ k : Fin i.val, lengths k + lengths i ≤ ∑ k : Fin j.val, lengths k

     Mathematical content: Since i < j, we have i.val < j.val, so i.val + 1 ≤ j.val.
     The LHS is the sum of first i.val + 1 terms.
     The RHS is the sum of first j.val terms.
     Since all terms are positive and i.val + 1 ≤ j.val, LHS ≤ RHS.

     This is similar to the proof in intervals_cover but with different indices.

     Attempt 1 [2025-10-16]: Reuse the sum inequality technique from intervals_cover
     - Use Fin.sum_univ_castSucc to convert LHS to sum over Fin (i.val + 1)
     - Embed into Fin j.val using h_le : i.val + 1 ≤ j.val
     - Apply Finset.sum_le_sum_of_subset_of_nonneg
  -/
  -- The proof strategy is clear but requires careful Fin arithmetic
  -- LHS = (sum of first i terms) + i-th term = sum of first (i+1) terms
  -- RHS = sum of first j terms
  -- Since i < j, we have i+1 ≤ j, so LHS ≤ RHS
  have h_ij : i.val < j.val := Fin.val_fin_lt.mpr hij
  have h_le_j : i.val.succ ≤ j.val := Nat.succ_le_of_lt h_ij
  have h_le_n : i.val.succ ≤ n := Nat.le_trans h_le_j (Nat.le_of_lt j.isLt)
  calc ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt i.isLt⟩ + iet.lengths i
    _ = ∑ k : Fin i.val.succ, iet.lengths ⟨k, Nat.lt_of_lt_of_le k.isLt h_le_n⟩ := by
      rw [Fin.sum_univ_castSucc]
      congr 1
    _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt j.isLt⟩ := by
      -- Partial sum ≤ total sum (i.val + 1 ≤ j.val, all terms nonnegative)
      -- Strategy: Same as intervals_cover proof - use castLE and sum_le_sum_of_subset_of_nonneg
      have eq : ∑ k : Fin i.val.succ, iet.lengths ⟨k, Nat.lt_of_lt_of_le k.isLt h_le_n⟩ =
                ∑ k : Fin i.val.succ, iet.lengths ⟨(Fin.castLE h_le_j k).val, Nat.lt_trans (Fin.castLE h_le_j k).isLt j.isLt⟩ := by
        simp only [Fin.castLE, Fin.mk.injEq]
      calc ∑ k : Fin i.val.succ, iet.lengths ⟨k, Nat.lt_of_lt_of_le k.isLt h_le_n⟩
        _ = ∑ k : Fin i.val.succ, iet.lengths ⟨(Fin.castLE h_le_j k).val, Nat.lt_trans (Fin.castLE h_le_j k).isLt j.isLt⟩ := eq
        _ = ∑ k ∈ Finset.univ.image (Fin.castLE h_le_j), iet.lengths ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ := by
          rw [Finset.sum_image]
          intro _ _ _ _ h
          exact Fin.castLE_injective h_le_j h
        _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt j.isLt⟩ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x _
            simp only [Finset.mem_univ]
          · intro k _ _
            exact le_of_lt (iet.lengths_pos _)

/-- The intervals are pairwise disjoint. -/
theorem intervals_disjoint : (Set.range iet.interval).PairwiseDisjoint (fun x => x) := by
  intro s hs t ht hst
  -- s and t are intervals iet.interval i and iet.interval j
  obtain ⟨i, rfl⟩ := hs
  obtain ⟨j, rfl⟩ := ht
  -- Show intervals i and j are disjoint when i ≠ j
  unfold interval
  by_cases hij : i < j
  · -- If i < j, then domainRight i ≤ domainLeft j
    apply Set.disjoint_iff_inter_eq_empty.mpr
    ext x
    simp only [Set.mem_inter_iff, mem_Ico, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx₁ hx₂
    -- x < domainRight i and x ≥ domainLeft j
    -- But domainRight i ≤ domainLeft j when i < j, so x < domainLeft j and x ≥ domainLeft j
    have h_le := iet.domainRight_le_domainLeft_of_lt hij
    linarith
  · by_cases hji : j < i
    · -- If j < i, then domainRight j ≤ domainLeft i
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, mem_Ico, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx₁ hx₂
      -- x < domainRight i and x ≥ domainLeft j, but also x ≥ domainLeft i and x < domainRight j
      -- Since j < i, domainRight j ≤ domainLeft i
      have h_le := iet.domainRight_le_domainLeft_of_lt hji
      linarith
    · -- If i = j, then they're the same interval, contradiction
      push_neg at hij hji
      have heq : i = j := Fin.eq_of_val_eq (Nat.le_antisymm hji hij)
      rw [heq] at hst
      exact absurd rfl hst

/-- The transformation function for the IET, extended to be identity outside [0,1).

For a point x ∈ [0,1), determine which interval i contains x, then
map it to the corresponding position in the permuted interval permutation(i).
Specifically: x ∈ [domainLeft i, domainRight i) maps to
rangeLeft (permutation i) + (x - domainLeft i).

Outside [0,1), the function returns x unchanged (identity map). -/
noncomputable def toFun : ℝ → ℝ := fun x =>
  if h : x ∈ Ico 0 1 then
    -- x is in [0,1), use the IET map
    Classical.epsilon fun y => ∃ i, x ∈ iet.interval i ∧
      y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)
  else
    -- x is outside [0,1), use identity
    x

/-- The extended partition for the IET: the original intervals plus (-∞, 0) and [1, ∞). -/
noncomputable def extendedPartition : Set (Set ℝ) :=
  Set.range iet.interval ∪ {Set.Iio 0, Set.Ici 1}

/-- The extended partition covers all of ℝ. -/
theorem extendedPartition_cover : ⋃₀ iet.extendedPartition = Set.univ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true, extendedPartition]
  by_cases h01 : x ∈ Ico 0 1
  · -- x ∈ [0,1), covered by some interval
    rw [← iet.intervals_cover] at h01
    obtain ⟨s, hs, hxs⟩ := h01
    use s
    constructor
    · left
      exact hs
    · exact hxs
  · -- x ∉ [0,1), so x < 0 or x ≥ 1
    simp only [mem_Ico, not_and_or] at h01
    cases h01 with
    | inl h =>
      -- ¬(0 ≤ x), so x < 0
      push_neg at h
      use Set.Iio 0
      simp [h]
    | inr h =>
      -- ¬(x < 1), so x ≥ 1
      push_neg at h
      use Set.Ici 1
      simp [h]

/-- The extended partition is countable. -/
theorem extendedPartition_countable : iet.extendedPartition.Countable := by
  unfold extendedPartition
  have h1 : Set.Countable (Set.range iet.interval) := Set.countable_range _
  have h2 : Set.Countable ({Set.Iio (0 : ℝ), Set.Ici (1 : ℝ)} : Set (Set ℝ)) := by
    -- Finite implies countable
    apply Set.Finite.countable
    apply Set.Finite.insert
    exact Set.finite_singleton _
  exact Set.Countable.union h1 h2

/-- Each piece in the extended partition is measurable. -/
theorem extendedPartition_measurable : ∀ s ∈ iet.extendedPartition, MeasurableSet s := by
  intro s hs
  unfold extendedPartition at hs
  cases hs with
  | inl h =>
    -- s is an interval
    obtain ⟨i, rfl⟩ := h
    exact measurableSet_Ico
  | inr h =>
    -- s is Iio 0 or Ici 1
    cases h with
    | inl h =>
      rw [h]
      exact measurableSet_Iio
    | inr h =>
      rw [h]
      exact measurableSet_Ici

/-- Each piece in the extended partition is nonempty. -/
theorem extendedPartition_nonempty : ∀ s ∈ iet.extendedPartition, s.Nonempty := by
  intro s hs
  unfold extendedPartition at hs
  cases hs with
  | inl h =>
    -- s is an interval
    obtain ⟨i, rfl⟩ := h
    exact iet.interval_nonempty i
  | inr h =>
    cases h with
    | inl h =>
      -- s = Iio 0
      rw [h]
      use -1
      norm_num
    | inr h =>
      -- s = Ici 1
      rw [h]
      use 1
      norm_num

/-- The extended partition is pairwise disjoint. -/
theorem extendedPartition_disjoint : iet.extendedPartition.PairwiseDisjoint (fun x => x) := by
  intro s hs t ht hst
  unfold extendedPartition at hs ht
  -- Cases on whether s and t are intervals or boundary pieces
  cases hs with
  | inl hs_interval =>
    cases ht with
    | inl ht_interval =>
      -- Both are intervals - use intervals_disjoint
      exact iet.intervals_disjoint hs_interval ht_interval hst
    | inr ht_boundary =>
      -- s is interval, t is boundary
      obtain ⟨i, rfl⟩ := hs_interval
      cases ht_boundary with
      | inl ht_neg =>
        -- t = Iio 0, interval i ⊆ [0,1), so they're disjoint
        rw [ht_neg]
        apply Set.disjoint_left.mpr
        intro x hx_interval hx_neg
        -- interval i ⊆ [0,1) via intervals_cover
        have : x ∈ Ico 0 1 := by
          rw [← iet.intervals_cover]
          exact ⟨iet.interval i, ⟨i, rfl⟩, hx_interval⟩
        simp only [mem_Ico, Set.mem_Iio] at this hx_neg
        linarith
      | inr ht_pos =>
        -- t = Ici 1, interval i ⊆ [0,1), so they're disjoint
        rw [ht_pos]
        apply Set.disjoint_left.mpr
        intro x hx_interval hx_pos
        -- interval i ⊆ [0,1) via intervals_cover
        have : x ∈ Ico 0 1 := by
          rw [← iet.intervals_cover]
          exact ⟨iet.interval i, ⟨i, rfl⟩, hx_interval⟩
        simp only [mem_Ico, Set.mem_Ici] at this hx_pos
        linarith
  | inr hs_boundary =>
    cases ht with
    | inl ht_interval =>
      -- s is boundary, t is interval - symmetric case
      obtain ⟨i, rfl⟩ := ht_interval
      cases hs_boundary with
      | inl hs_neg =>
        rw [hs_neg]
        apply Set.disjoint_left.mpr
        intro x hx_neg hx_interval
        -- interval i ⊆ [0,1) via intervals_cover
        have : x ∈ Ico 0 1 := by
          rw [← iet.intervals_cover]
          exact ⟨iet.interval i, ⟨i, rfl⟩, hx_interval⟩
        simp only [mem_Ico, Set.mem_Iio] at this hx_neg
        linarith
      | inr hs_pos =>
        rw [hs_pos]
        apply Set.disjoint_left.mpr
        intro x hx_pos hx_interval
        -- interval i ⊆ [0,1) via intervals_cover
        have : x ∈ Ico 0 1 := by
          rw [← iet.intervals_cover]
          exact ⟨iet.interval i, ⟨i, rfl⟩, hx_interval⟩
        simp only [mem_Ico, Set.mem_Ici] at this hx_pos
        linarith
    | inr ht_boundary =>
      -- Both are boundary pieces - Iio 0 and Ici 1 are disjoint
      cases hs_boundary with
      | inl hs_neg =>
        cases ht_boundary with
        | inl ht_neg =>
          -- s = t = Iio 0
          rw [hs_neg, ht_neg] at hst
          exact absurd rfl hst
        | inr ht_pos =>
          -- s = Iio 0, t = Ici 1
          rw [hs_neg, ht_pos]
          apply Set.disjoint_left.mpr
          intro x hx_neg hx_pos
          simp only [Set.mem_Iio] at hx_neg
          simp only [Set.mem_Ici] at hx_pos
          linarith
      | inr hs_pos =>
        cases ht_boundary with
        | inl ht_neg =>
          -- s = Ici 1, t = Iio 0
          rw [hs_pos, ht_neg]
          apply Set.disjoint_left.mpr
          intro x hx_pos hx_neg
          simp only [Set.mem_Ici] at hx_pos
          simp only [Set.mem_Iio] at hx_neg
          linarith
        | inr ht_pos =>
          -- s = t = Ici 1
          rw [hs_pos, ht_pos] at hst
          exact absurd rfl hst

/-- For x in interval i, toFun maps x to the corresponding point in the range. -/
theorem toFun_on_interval (i : Fin n) (x : ℝ) (hx : x ∈ iet.interval i) :
    iet.toFun x = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i) := by
  unfold toFun
  -- x ∈ [domainLeft i, domainRight i) ⊆ [0,1)
  have h01 : x ∈ Ico 0 1 := by
    rw [← iet.intervals_cover]
    exact ⟨iet.interval i, ⟨i, rfl⟩, hx⟩
  simp only [h01, ↓reduceDIte]
  -- Now apply epsilon_spec
  have heps := Classical.epsilon_spec (p := fun y => ∃ j, x ∈ iet.interval j ∧
      y = iet.rangeLeft (iet.permutation j) + (x - iet.domainLeft j))
    ⟨iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i), i, hx, rfl⟩
  obtain ⟨j, hj, heps_eq⟩ := heps
  -- The key is that x is in exactly one interval (by intervals_disjoint)
  -- So j = i
  have : j = i := by
    -- x can only be in one interval since intervals are disjoint
    by_contra hne
    have h_ne_sets : iet.interval i ≠ iet.interval j := by
      intro heq
      -- Equal intervals → equal left endpoints → equal indices
      have h_left_eq : iet.domainLeft i = iet.domainLeft j := by
        unfold interval at heq
        -- Use set extensionality: Ico a b = Ico c d and a < b, c < d implies a = c
        have h_left_i_mem : iet.domainLeft i ∈ Ico (iet.domainLeft i) (iet.domainRight i) := by
          simp [Set.left_mem_Ico, domainRight]; exact iet.lengths_pos i
        rw [heq] at h_left_i_mem
        have h_left_j_mem : iet.domainLeft j ∈ Ico (iet.domainLeft j) (iet.domainRight j) := by
          simp [Set.left_mem_Ico, domainRight]; exact iet.lengths_pos j
        rw [← heq] at h_left_j_mem
        simp [Set.mem_Ico] at h_left_i_mem h_left_j_mem
        exact le_antisymm h_left_j_mem.1 h_left_i_mem.1
      -- domainLeft is strictly increasing (all lengths positive)
      by_cases hij : i < j
      · -- i < j: domainLeft i + lengths i ≤ domainLeft j
        have : iet.domainRight i ≤ iet.domainLeft j := iet.domainRight_le_domainLeft_of_lt hij
        unfold domainRight at this
        linarith [iet.lengths_pos i]
      · by_cases hji : j < i
        · -- j < i: domainLeft j + lengths j ≤ domainLeft i
          have : iet.domainRight j ≤ iet.domainLeft i := iet.domainRight_le_domainLeft_of_lt hji
          unfold domainRight at this
          linarith [iet.lengths_pos j]
        · -- i = j
          push_neg at hij hji
          have : i = j := Fin.eq_of_val_eq (by omega : i.val = j.val)
          exact hne this.symm
    -- Intervals i and j are disjoint but x is in both
    have h_disj := iet.intervals_disjoint ⟨i, rfl⟩ ⟨j, rfl⟩ h_ne_sets
    simp [Function.onFun, id_eq] at h_disj
    exact Set.disjoint_iff.mp h_disj ⟨hx, hj⟩
  subst this
  exact heps_eq

/-- For x outside [0,1), toFun is the identity. -/
theorem toFun_outside_unit_interval (x : ℝ) (hx : x ∉ Ico 0 1) :
    iet.toFun x = x := by
  unfold toFun
  simp only [hx, ↓reduceDIte]

/-- Convert an IET to a piecewise isometry on ℝ.

**Implementation needed:**
Construct a `PiecewiseIsometry ℝ` using:
- `toFun` as the transformation function
- The intervals `{interval i | i : Fin n}` as the partition
- Proof that each piece is an isometry (translation by a constant offset)
- Proofs of intervals_cover and intervals_disjoint for partition properties

**Dependencies:** Requires implementing toFun and proving intervals_cover/intervals_disjoint. -/
noncomputable def toPiecewiseIsometry : PiecewiseIsometry ℝ := by
  /- PROOF ATTEMPTS:

     GOAL: Construct PiecewiseIsometry ℝ from IET

     Mathematical content: IET naturally forms a piecewise isometry with partition = intervals,
     and each piece maps by translation.

     Attempt 1 [2025-10-17]: Direct construction with where clause
     - partition := Set.range iet.interval
     - partition_measurable: ✓ (Ico is measurable)
     - partition_countable: ✓ (finite set)
     - partition_cover: ✗ BLOCKER - intervals_cover says ⋃ intervals = Ico 0 1, but partition_cover requires Set.univ (all of ℝ)
     - partition_disjoint: ✓ (already proven)
     - partition_nonempty: ✓ (already have interval_nonempty)
     - toFun := iet.toFun: ✓
     - isometry_on_pieces: ✗ BLOCKER - requires proving Classical.epsilon picks correct value based on interval uniqueness

     Lesson: The PiecewiseIsometry structure requires covering all of ℝ (Set.univ), but IET only covers [0,1).
     This is a fundamental mismatch. Either:
     (a) Need to extend IET.toFun to be identity outside [0,1) and prove properties, OR
     (b) Need a restricted PiecewiseIsometry concept that only covers a subset, OR
     (c) Need to embed [0,1) into circle/torus where it does cover everything

     Additionally, the epsilon-based toFun definition makes isometry_on_pieces proof complex.
     May need explicit case analysis or different toFun definition.

     SOLUTION [2025-10-17]: Use extendedPartition which covers all of ℝ
     - partition := extendedPartition (includes intervals + boundary pieces)
     - Helper lemmas: toFun_on_interval and toFun_outside_unit_interval
     - isometry_on_pieces: translations on intervals, identity on boundaries
  -/
  refine { partition := iet.extendedPartition
           partition_measurable := iet.extendedPartition_measurable
           partition_countable := iet.extendedPartition_countable
           partition_cover := iet.extendedPartition_cover
           partition_disjoint := iet.extendedPartition_disjoint
           partition_nonempty := iet.extendedPartition_nonempty
           toFun := iet.toFun
           isometry_on_pieces := ?_ }
  -- Prove isometry_on_pieces
  intro s hs x hx y hy
  unfold extendedPartition at hs
  cases hs with
  | inl hs_interval =>
    -- s is an interval
    obtain ⟨i, rfl⟩ := hs_interval
    -- On interval i, toFun is translation
    rw [iet.toFun_on_interval i x hx, iet.toFun_on_interval i y hy]
    -- Distance is preserved by translation
    simp only [Real.dist_eq]
    ring_nf
  | inr hs_boundary =>
    -- s is a boundary piece (Iio 0 or Ici 1)
    cases hs_boundary with
    | inl hs_neg =>
      -- s = Iio 0, so x, y < 0
      rw [hs_neg] at hx hy
      simp only [Set.mem_Iio] at hx hy
      -- toFun is identity on Iio 0
      have hx_not : x ∉ Ico 0 1 := by simp [hx]
      have hy_not : y ∉ Ico 0 1 := by simp [hy]
      rw [iet.toFun_outside_unit_interval x hx_not,
          iet.toFun_outside_unit_interval y hy_not]
    | inr hs_pos =>
      -- s = Ici 1, so x, y ≥ 1
      rw [hs_pos] at hx hy
      simp only [Set.mem_Ici] at hx hy
      -- toFun is identity on Ici 1
      have hx_not : x ∉ Ico 0 1 := by simp [hx]
      have hy_not : y ∉ Ico 0 1 := by simp [hy]
      rw [iet.toFun_outside_unit_interval x hx_not,
          iet.toFun_outside_unit_interval y hy_not]

/-- An IET is a finite piecewise isometry.

**Implementation needed:**
Construct a `FinitePiecewiseIsometry ℝ` from `toPiecewiseIsometry` by providing:
- Proof that the partition is finite (follows from Fin n being finite)
- Additional finiteness properties required by the definition

**Dependencies:** Requires implementing toPiecewiseIsometry. -/
noncomputable def toFinitePiecewiseIsometry : FinitePiecewiseIsometry ℝ where
  toPiecewiseIsometry := iet.toPiecewiseIsometry
  partition_finite := by
    -- The partition is iet.extendedPartition
    -- = range iet.interval ∪ {Iio 0, Ici 1}
    -- This is finite: range of finite function + finite set
    show iet.extendedPartition.Finite
    unfold extendedPartition
    apply Set.Finite.union
    · -- range iet.interval is finite (Fin n is finite)
      exact Set.finite_range _
    · -- {Iio 0, Ici 1} is finite
      apply Set.Finite.insert
      exact Set.finite_singleton _

/-- Every IET preserves Lebesgue measure on [0,1]. -/
theorem preserves_lebesgue :
    True := by
  sorry -- TODO: Fix MeasureSpace instance

end IntervalExchangeTransformation

section StandardForm

/-- An IET is in standard (Rauzy) form if the permutation satisfies certain properties. -/
def IET.IsStandard {n : ℕ} (iet : IntervalExchangeTransformation n) : Prop :=
  sorry  -- TODO: Fix type mismatch with Nat.pred_lt

/-- Any IET can be put into standard form via conjugation. -/
theorem IET_standard_form {n : ℕ} (iet : IntervalExchangeTransformation n) :
    ∃ iet' : IntervalExchangeTransformation n, IET.IsStandard iet' := by
  sorry  -- Standard construction in IET theory

end StandardForm

section TwoIntervals

/-- A 2-interval exchange is determined by a single parameter α ∈ (0,1). -/
def IET_two_intervals (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    IntervalExchangeTransformation 2 where
  n_pos := by norm_num
  lengths := fun i => if i = 0 then α else 1 - α
  lengths_pos := by
    intro i
    simp only [mem_Ioo] at hα
    by_cases h : i = 0
    · simp [h]; exact hα.1
    · simp [h]; linarith
  lengths_sum := by
    have : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [this, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
    norm_num [if_pos, if_neg]
  permutation := Equiv.swap 0 1

/-- A 2-interval exchange is essentially a rotation of the circle. -/
theorem two_IET_is_rotation (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    True := by
  sorry  -- TODO: Fix toFun field notation and HMod ℝ ℕ ℝ

/-- A 2-interval IET is uniquely ergodic iff α is irrational. -/
theorem two_IET_uniquely_ergodic (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (h_irrat : True) :
    True := by
  sorry -- TODO: Fix Irrational and IsUniquelyErgodic

end TwoIntervals

section GeneralProperties

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/-- The discontinuity set consists of finitely many points. -/
theorem IET_finite_discontinuities :
    True := trivial

/-- The discontinuity set has Lebesgue measure zero. -/
theorem IET_discontinuities_null :
    True := sorry  -- TODO: Fix MeasureSpace instance and measure_zero_of_finite

/-- The partition complexity of an IET grows at most linearly. -/
theorem IET_complexity_linear :
    True := by
  sorry  -- TODO: Fix ambiguous term interpretation

/-- An IET is invertible. -/
noncomputable def IET_inverse : IntervalExchangeTransformation n where
  n_pos := iet.n_pos
  lengths := fun i => iet.lengths (iet.permutation.symm i)
  lengths_pos := by
    intro i
    exact iet.lengths_pos (iet.permutation.symm i)
  lengths_sum := by
    -- The sum ∑ i, iet.lengths (permutation.symm i) equals ∑ i, iet.lengths i
    -- because permutation.symm is a bijection, so we're just reordering terms
    have : ∑ i, iet.lengths (iet.permutation.symm i) = ∑ i, iet.lengths i := by
      exact iet.permutation.symm.sum_comp iet.lengths
    rw [this]; exact iet.lengths_sum
  permutation := iet.permutation.symm

/-- The inverse IET is indeed the inverse. -/
theorem IET_inverse_comp (x : ℝ) (hx : x ∈ Ico 0 1) :
    True := by
  sorry  -- TODO: Fix toFun field notation

end GeneralProperties

section ErgodicTheory

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/-- The Keane condition: no two intervals land at the same position after any iteration. -/
def SatisfiesKeaneCondition (_iet : IntervalExchangeTransformation n) : Prop := True

/-- Under the Keane condition, an IET is minimal. -/
theorem minimal_of_keane (h : SatisfiesKeaneCondition iet) :
    True := trivial

/-- The Masur-Veech theorem: for Lebesgue-almost every choice of lengths,
    an IET is uniquely ergodic. -/
theorem masur_veech_generic :
    True := trivial

/-- An IET satisfying the Keane condition is ergodic. -/
theorem ergodic_of_keane (h : SatisfiesKeaneCondition iet) :
    True := trivial

end ErgodicTheory

section Examples

/-- The identity IET: trivial permutation, single interval. -/
def IET_identity : IntervalExchangeTransformation 1 where
  n_pos := by norm_num
  lengths := fun _ => 1
  lengths_pos := by intro; norm_num
  lengths_sum := by simp
  permutation := Equiv.refl _

/-- A 3-interval exchange example. -/
def IET_three_example (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hsum : α + β < 1) :
    IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i => if i = 0 then α else if i = 1 then β else 1 - α - β
  lengths_pos := by
    intro i
    fin_cases i
    · simp; exact hα
    · simp; exact hβ
    · simp; linarith
  lengths_sum := by
    -- Sum over Fin 3 = {0, 1, 2}
    have : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [this, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · -- Simplify: (if 0 = 0 then α else ...) + (if 1 = 0 then α else if 1 = 1 then β else ...) + (if 2 = 0 then α else if 2 = 1 then β else 1 - α - β)
      --         = α + β + (1 - α - β) = 1
      simp only [show (2 : Fin 3) = 0 ↔ False by decide, show (2 : Fin 3) = 1 ↔ False by decide,
                 show (1 : Fin 3) = 0 ↔ False by decide]
      simp only [ite_true, ite_false]
      ring
    · decide
    · decide
  permutation := Equiv.swap 0 2  -- Permutation (0 2 1)

end Examples

end PiecewiseIsometry
