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
                -- Strategy: Map Fin i.val.succ into Fin n via castLE, then use sum_le_sum_of_subset_of_nonneg
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
  · -- If 0 ≤ x < 1, then x is in some interval
    intro ⟨hx0, hx1⟩
    /- PROOF ATTEMPTS:

       GOAL: Find i such that domainLeft i ≤ x < domainRight i

       Strategy: Use proof by contradiction. If x is not in any interval, derive a contradiction.
       Since intervals partition [0,1) and x ∈ [0,1), x must be in some interval.

       Attempt 1 [2025-10-16]: Use Finset.exists_max_image
       - Issue: Need to convert between Set and Finset, handle subtypes
       - Complexity: High, many type coercions

       Attempt 2 [2025-10-16]: Direct construction using if-then-else
       - Strategy: Use classical choice or decidability to pick the interval
       - Issue: Lean prefers constructive proofs when possible

       Attempt 3 [2025-10-17]: Proof by contradiction using finite case analysis
       - Strategy: Show that if x is not in any interval, we get a contradiction
       - Use: Fintype.exists_of_not_forall_not or direct decidability
    -/
    -- Strategy: Since Fin n is decidable and finite, we can decide for each i
    -- whether x ∈ interval i. Since x ∈ [0,1) and intervals cover [0,1),
    -- at least one such i must exist.

    -- Key lemmas we'll need:
    -- domainLeft 0 = 0
    have h_left_0 : iet.domainLeft ⟨0, iet.n_pos⟩ = 0 := by
      unfold domainLeft
      simp

    -- Find interval containing x by strong induction on i
    -- We look for the largest i such that domainLeft i ≤ x
    -- Then x < domainRight i by contiguity and the fact that x < 1

    -- Use decidability: for each i, decide if x < domainRight i
    -- The minimal such i is our interval
    have h_minimal_exists : ∃ i : Fin n, x < iet.domainRight i ∧
        ∀ j : Fin n, j < i → iet.domainRight j ≤ x := by
      -- First show existence: there is some i with x < domainRight i
      -- Since x < 1 and sum of all lengths = 1, we have x < domainRight (n-1)
      have h_exists_some : ∃ i : Fin n, x < iet.domainRight i := by
        -- The last interval has domainRight = 1
        have h_n_minus_1_lt : n - 1 < n := Nat.pred_lt (Nat.pos_iff_ne_zero.mp iet.n_pos)
        have h_last : iet.domainRight ⟨n - 1, h_n_minus_1_lt⟩ = 1 := by
          unfold domainRight domainLeft
          -- Goal: (∑ j : Fin (n-1), lengths j) + lengths ⟨n-1, _⟩ = 1
          -- Need to show this equals ∑ j : Fin n, lengths j = 1

          -- The key is that ∑ j < n-1, lengths j + lengths (n-1) = ∑ j < n, lengths j = 1
          -- This requires using Fin.sum_univ_castSucc or a similar decomposition lemma
          -- The challenge is the dependent types: Fin (n-1) vs Fin n

          -- Attempt 7 [2025-10-17]: Finset.sum_bij to establish the equality directly
          -- Goal: ∑ j : Fin (n-1), lengths ⟨j, _⟩ + lengths ⟨n-1, _⟩ = 1

          -- We'll show LHS = ∑ j : Fin n, lengths j = 1
          rw [← iet.lengths_sum]

          -- Use Finset.sum_bij to show the sums are equal
          -- The idea: Fin n can be partitioned into Fin (n-1) (via castSucc) ∪ {last}

          -- First, simplify the sum on LHS to have uniform form
          have h_sum_eq : ∑ j : Fin (n - 1), iet.lengths ⟨↑j, Nat.lt_trans j.isLt h_n_minus_1_lt⟩ =
                          ∑ j : Fin (n - 1), iet.lengths ⟨j.val, by omega⟩ := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1

          rw [h_sum_eq]
          clear h_sum_eq

          -- Now use that Fin n = image of castSucc from Fin (n-1) ∪ {last (n-1)}
          -- Express ∑ over Fin n as sum over this partition

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
          · -- Disjointness
            simp only [Finset.disjoint_singleton_right, Finset.mem_image, not_exists, not_and]
            intro j _ h
            have : j.val = n - 1 := Fin.mk_eq_mk.mp h
            omega
        use ⟨n - 1, h_n_minus_1_lt⟩
        rw [h_last]
        exact hx1
      -- Now use well-foundedness to find the minimal i
      -- Use Nat.find to find the minimal k < n such that x < domainRight ⟨k, _⟩
      -- Then convert to Fin n

      -- Use Nat.find with explicit decidable instance
      -- The predicate: k < n and x < domainRight ⟨k, _⟩
      have h_dec : ∀ k, Decidable (k < n) := inferInstance

      -- Since Fin n is finite and we have decidable equality/ordering, we can find the minimum
      -- We'll use a simpler approach: extract the finite set and use Finset.min'

      -- Convert to Finset approach
      let S : Finset (Fin n) := Finset.univ.filter (fun i => x < iet.domainRight i)

      have hS_nonempty : S.Nonempty := by
        obtain ⟨i, hi⟩ := h_exists_some
        use i
        simp [S]
        exact hi

      -- Get the minimal element
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

    -- Show that x ≥ domainLeft i
    have hi_lower : iet.domainLeft i ≤ x := by
      -- Case analysis on whether i = 0
      by_cases h_i_zero : i.val = 0
      · -- Case i = 0: domainLeft 0 = 0 ≤ x
        have : i = ⟨0, by omega⟩ := Fin.ext h_i_zero
        rw [this, h_left_0]
        exact hx0
      · -- Case i > 0: Use contiguity and minimality
        -- Since i > 0, we have i = (i-1) + 1
        -- By contiguity: domainRight (i-1) = domainLeft i
        -- By minimality: ∀ j < i, domainRight j ≤ x
        -- So domainRight (i-1) ≤ x, hence domainLeft i ≤ x

        have h_i_pos : 0 < i.val := by omega
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

        -- Contiguity: domainRight (i-1) = domainLeft i
        -- We'll show both equal the same intermediate value
        have h_contiguity : iet.domainRight i_pred = iet.domainLeft i := by
          unfold domainRight domainLeft
          -- Use that i = ⟨i_pred.val + 1, _⟩
          have h_i_as_succ : ∃ h, i = ⟨i_pred.val + 1, h⟩ := by
            use h_i_succ_lt
            ext
            simp [i_pred]
            omega
          obtain ⟨h_i_bound, h_i_eq⟩ := h_i_as_succ
          rw [h_i_eq]
          -- Now apply Fin.sum_univ_castSucc
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
  -- Sum over Fin i.val < sum over Fin j.val since i.val < j.val and extra terms are positive
  have h_i_lt_n : i.val < n := i.isLt
  have h_j_lt_n : j.val < n := j.isLt
  have h_ival_lt_jval : i.val < j.val := hij
  have h_succ_le : i.val.succ ≤ j.val := h_ival_lt_jval
  calc ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_i_lt_n⟩
      < ∑ k : Fin i.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_i_lt_n⟩ + iet.lengths ⟨i.val, Nat.lt_trans h_ival_lt_jval h_j_lt_n⟩ := by
        linarith [iet.lengths_pos ⟨i.val, Nat.lt_trans h_ival_lt_jval h_j_lt_n⟩]
    _ ≤ ∑ k : Fin j.val, iet.lengths ⟨k, Nat.lt_trans k.isLt h_j_lt_n⟩ := by
        -- Similar to the proof in intervals_cover
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
  -- Sum over Fin i.val ≤ sum over Fin j.val when i.val ≤ j.val
  -- This is a partial sum inequality: all terms are nonnegative
  by_cases h_eq : i = j
  · rw [h_eq]
  · have hij_strict : i.val < j.val := Nat.lt_of_le_of_ne hij (fun h => h_eq (Fin.eq_of_val_eq h))
    -- ∑ k < i.val ≤ ∑ k < j.val since i.val ≤ j.val and extra terms are ≥ 0
    -- Map Fin i.val into Fin j.val via castLE, show it's a subset, use sum_le_sum_of_subset_of_nonneg
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
  -- Need to show: (∑ j : Fin i.val, lengths j) + lengths i = ∑ j : Fin (i.val + 1), lengths j
  rw [Fin.sum_univ_castSucc]
  congr 1

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

     Attempt 2 [2025-10-17]: Direct application of technique from line 165
     - Use Fin.sum_univ_castSucc, Fin.castLE, and Finset.sum_le_sum_of_subset_of_nonneg
     - Partial progress, but type complexity with Fin coercions became unwieldy

     Attempt 3 [2025-10-17]: Simplify with Fin.sum_univ_castSucc directly
     - Issue: The sum in goal has explicit type annotations that don't match Fin.sum_univ_castSucc pattern
     - Lesson: Need to either change representation or find lemma that works with annotated Fin sums
  -/
  -- Mathematical idea: domainRight i = sum of first (i+1) terms
  -- domainLeft j = sum of first j terms
  -- Since i < j, we have i+1 ≤ j, so first sum ≤ second sum (all terms positive)

  -- The core issue is proving: ∑_{k < i.val} f k + f i ≤ ∑_{k < j.val} f k
  -- where f k = lengths ⟨k, proof⟩

  -- We'll use transitivity via the contiguity property
  by_cases h_succ_eq : i.val.succ = j.val
  · -- Case 1: i.val + 1 = j.val, i.e., i and j are consecutive
    -- Then domainRight i = domainLeft j by contiguity
    have h_cons : i.val + 1 < n := by
      calc i.val + 1 = j.val := h_succ_eq
        _ < n := j.isLt
    have : ⟨i.val.succ, h_cons⟩ = j := by
      ext
      simp [Nat.succ_eq_add_one]
      exact h_succ_eq
    rw [← this]
    exact le_of_eq (iet.domainRight_eq_domainLeft_succ i h_cons)
  · -- Case 2: i.val + 1 < j.val
    have h_succ_lt : i.val.succ < j.val := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hij) h_succ_eq
    -- domainRight i = domainLeft (i+1) ≤ domainLeft j
    have h_cons : i.val + 1 < n := Nat.lt_trans h_succ_lt j.isLt
    have h_le : ⟨i.val + 1, h_cons⟩ ≤ j := by
      show (⟨i.val + 1, h_cons⟩ : Fin n).val ≤ j.val
      exact Nat.le_of_lt h_succ_lt
    calc iet.domainRight i
        = iet.domainLeft ⟨i.val + 1, h_cons⟩ := iet.domainRight_eq_domainLeft_succ i h_cons
      _ ≤ iet.domainLeft j := iet.domainLeft_mono h_le

/-- Helper: which interval contains a point in [0,1). -/
noncomputable def intervalContaining (x : ℝ) (hx : x ∈ Ico 0 1) : Fin n :=
  Classical.choose (by
    have : x ∈ ⋃ i, iet.interval i := by rw [iet.intervals_cover]; exact hx
    simp only [Set.mem_iUnion] at this
    exact this)

/-- The chosen interval actually contains the point. -/
lemma mem_intervalContaining (x : ℝ) (hx : x ∈ Ico 0 1) :
    x ∈ interval iet (intervalContaining iet x hx) :=
  Classical.choose_spec (by
    have : x ∈ ⋃ i, iet.interval i := by rw [iet.intervals_cover]; exact hx
    simp only [Set.mem_iUnion] at this
    exact this)

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

/-- The interval function is injective. -/
lemma interval_injective : Function.Injective (interval iet) := by
  intro i j h_eq
  -- If interval i = interval j, then their left endpoints are equal
  -- interval i = Ico (domainLeft i) (domainRight i)
  unfold interval at h_eq
  -- Now h_eq : Ico (domainLeft i) (domainRight i) = Ico (domainLeft j) (domainRight j)
  -- Use trichotomy on i and j
  by_cases hij : i < j
  · -- If i < j, then domainLeft i < domainLeft j (by strict monotonicity)
    have h_left_lt : iet.domainLeft i < iet.domainLeft j := iet.domainLeft_strictMono hij
    -- From h_eq, extract that the left endpoints are equal
    -- domainLeft i is the infimum of Ico (domainLeft i) (domainRight i)
    -- If the intervals are equal, their infima are equal
    have h_left_eq : iet.domainLeft i = iet.domainLeft j := by
      -- Use the fact that domainLeft i ∈ Ico (domainLeft i) (domainRight i)
      -- and this is the smallest element
      have h_i_mem : iet.domainLeft i ∈ Ico (iet.domainLeft i) (iet.domainRight i) := by
        rw [mem_Ico]
        constructor
        · rfl
        · simp only [domainRight]
          linarith [iet.lengths_pos i]
      -- By h_eq, domainLeft i ∈ Ico (domainLeft j) (domainRight j)
      rw [h_eq] at h_i_mem
      rw [mem_Ico] at h_i_mem
      -- So domainLeft j ≤ domainLeft i < domainRight j
      have h_j_le_i : iet.domainLeft j ≤ iet.domainLeft i := h_i_mem.1
      -- Similarly, domainLeft j ∈ Ico (domainLeft j) (domainRight j)
      have h_j_mem : iet.domainLeft j ∈ Ico (iet.domainLeft j) (iet.domainRight j) := by
        rw [mem_Ico]
        constructor
        · rfl
        · simp only [domainRight]
          linarith [iet.lengths_pos j]
      -- By h_eq.symm, domainLeft j ∈ Ico (domainLeft i) (domainRight i)
      rw [← h_eq] at h_j_mem
      rw [mem_Ico] at h_j_mem
      -- So domainLeft i ≤ domainLeft j
      have h_i_le_j : iet.domainLeft i ≤ iet.domainLeft j := h_j_mem.1
      -- Therefore domainLeft i = domainLeft j
      exact le_antisymm h_i_le_j h_j_le_i
    -- But we also have domainLeft i < domainLeft j, contradiction
    linarith
  · by_cases hji : j < i
    · -- If j < i, symmetric argument: domainLeft j < domainLeft i but they must be equal
      have h_left_lt : iet.domainLeft j < iet.domainLeft i := iet.domainLeft_strictMono hji
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
    · -- If neither i < j nor j < i, then i = j
      push_neg at hij hji
      exact Fin.eq_of_val_eq (Nat.le_antisymm hji hij)

/-- If x is in interval i, then intervalContaining returns i (by uniqueness). -/
lemma intervalContaining_unique (x : ℝ) (hx : x ∈ Ico 0 1) (i : Fin n) (hi : x ∈ interval iet i) :
    intervalContaining iet x hx = i := by
  -- Both intervals contain x, and intervals are disjoint, so they must be the same
  have h_mem := mem_intervalContaining iet x hx
  by_contra h_ne
  -- intervals are disjoint when indices differ
  have h_disj := iet.intervals_disjoint (Set.mem_range_self (intervalContaining iet x hx))
                                       (Set.mem_range_self i)
                                       (by intro h_eq; exact h_ne (iet.interval_injective h_eq))
  have : x ∈ interval iet (intervalContaining iet x hx) ∩ interval iet i := ⟨h_mem, hi⟩
  exact Set.disjoint_iff_inter_eq_empty.mp h_disj |>.subset this

/-- The transformation function for the IET.

For a point x ∈ [0,1), determine which interval i contains x, then
map it to the corresponding position in the permuted interval permutation(i).
Specifically: x ∈ [domainLeft i, domainRight i) maps to
rangeLeft (permutation i) + (x - domainLeft i).

Outside [0,1), the function returns x unchanged. -/
noncomputable def toFun : ℝ → ℝ := fun x =>
  Classical.epsilon fun y => ∃ i, x ∈ iet.interval i ∧
    y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)

/-- Convert an IET to a piecewise isometry on ℝ.

The IET naturally operates on [0,1). To extend to all of ℝ, we add two additional pieces:
- Iio 0 (negative reals): toFun acts as identity
- Ici 1 (≥ 1): toFun acts as identity

This matches the standard pattern for extending interval transformations to full space. -/
noncomputable def toPiecewiseIsometry : PiecewiseIsometry ℝ where
  partition := Set.range iet.interval ∪ {Set.Iio 0, Set.Ici 1}
  partition_measurable := by
    intro s hs
    simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with ⟨i, rfl⟩ | rfl | rfl
    · -- interval i is measurable (it's Ico a b)
      unfold interval
      exact measurableSet_Ico
    · -- Iio 0 is measurable
      exact measurableSet_Iio
    · -- Ici 1 is measurable
      exact measurableSet_Ici
  partition_countable := by
    apply Set.Countable.union
    · exact Set.countable_range _
    · apply Set.Countable.insert
      exact Set.countable_singleton _
  partition_cover := by
    ext x
    simp only [Set.mem_sUnion, Set.mem_union, Set.mem_range, Set.mem_insert_iff,
               Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hx0 : x < 0
    · -- x < 0: in Iio 0
      use Set.Iio 0
      constructor
      · right; left; rfl
      · exact Set.mem_Iio.mpr hx0
    · push_neg at hx0
      by_cases hx1 : x < 1
      · -- x ∈ [0,1), so x is in some interval i
        have : x ∈ Ico 0 1 := Set.mem_Ico.mpr ⟨hx0, hx1⟩
        rw [← iet.intervals_cover] at this
        simp only [Set.mem_iUnion] at this
        obtain ⟨i, hi⟩ := this
        use iet.interval i
        constructor
        · left; exact Set.mem_range_self i
        · exact hi
      · -- x ≥ 1: in Ici 1
        push_neg at hx1
        use Set.Ici 1
        constructor
        · right; right; rfl
        · exact Set.mem_Ici.mpr hx1
  partition_disjoint := by
    intro s hs t ht hst
    simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with ⟨i, rfl⟩ | rfl | rfl <;> rcases ht with ⟨j, rfl⟩ | rfl | rfl
    · -- interval i vs interval j
      by_cases hij : i = j
      · rw [hij] at hst; exact absurd rfl hst
      · exact iet.intervals_disjoint (Set.mem_range_self i) (Set.mem_range_self j)
                                     (by intro heq; exact hij (iet.interval_injective heq))
    · -- interval i vs Iio 0
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, id_eq]
      intro hx_int hx_neg
      have hx_int' : x ∈ interval iet i := hx_int
      simp only [interval, Set.mem_Ico, Set.mem_Iio] at hx_int' hx_neg
      have h_left_nn : 0 ≤ iet.domainLeft i := by
        unfold domainLeft
        apply Finset.sum_nonneg
        intro j _
        exact le_of_lt (iet.lengths_pos _)
      linarith
    · -- interval i vs Ici 1
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, id_eq]
      intro hx_int hx_ge
      have hx_int' : x ∈ interval iet i := hx_int
      simp only [interval, Set.mem_Ico, Set.mem_Ici] at hx_int' hx_ge
      have h_in_01 : x ∈ Ico 0 1 := by
        rw [← iet.intervals_cover]
        exact Set.mem_iUnion_of_mem i hx_int
      linarith [h_in_01.2, hx_ge]
    · -- Iio 0 vs interval j (symmetric)
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, id_eq]
      intro hx_neg hx_int
      have hx_int' : x ∈ interval iet j := hx_int
      simp only [Set.mem_Iio, interval, Set.mem_Ico] at hx_neg hx_int'
      have h_left_nn : 0 ≤ iet.domainLeft j := by
        unfold domainLeft
        apply Finset.sum_nonneg
        intro k _
        exact le_of_lt (iet.lengths_pos _)
      linarith
    · -- Iio 0 vs Iio 0
      exact absurd rfl hst
    · -- Iio 0 vs Ici 1
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
                 iff_false, not_and, id_eq]
      intro hx_neg hx_ge
      linarith
    · -- Aci 1 vs interval j (symmetric)
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, id_eq]
      intro hx_ge hx_int
      have hx_int' : x ∈ interval iet j := hx_int
      simp only [Set.mem_Ici, interval, Set.mem_Ico] at hx_ge hx_int'
      have h_in_01 : x ∈ Ico 0 1 := by
        rw [← iet.intervals_cover]
        exact Set.mem_iUnion_of_mem j hx_int
      linarith [h_in_01.2, hx_ge]
    · -- Ici 1 vs Iio 0 (symmetric)
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
                 iff_false, not_and, id_eq]
      intro hx_ge hx_neg
      linarith
    · -- Ici 1 vs Ici 1
      exact absurd rfl hst
  partition_nonempty := by
    intro s hs
    simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with ⟨i, rfl⟩ | rfl | rfl
    · exact iet.interval_nonempty i
    · use (-1); norm_num
    · use 1; norm_num
  toFun := fun x =>
    if h : x ∈ Ico 0 1 then
      -- x is in [0,1), so it's in some interval i
      -- Map it according to the IET
      let i := intervalContaining iet x h
      iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)
    else
      -- x is outside [0,1), act as identity
      x
  isometry_on_pieces := by
    intro s hs x hxs y hys
    simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with ⟨i, rfl⟩ | rfl | rfl
    · -- On interval i: the function is a translation
      have hxs' : x ∈ interval iet i := hxs
      have hys' : y ∈ interval iet i := hys
      simp only [interval, Set.mem_Ico] at hxs' hys'
      -- Both x and y are in [0,1)
      have hx_in : x ∈ Ico 0 1 := by
        rw [← iet.intervals_cover]
        exact Set.mem_iUnion_of_mem i hxs
      have hy_in : y ∈ Ico 0 1 := by
        rw [← iet.intervals_cover]
        exact Set.mem_iUnion_of_mem i hys
      -- Simplify the definition of toFun for x and y
      simp only [hx_in, hy_in, dif_pos]
      -- Show that intervalContaining gives us interval i for both x and y
      have hx_i : intervalContaining iet x hx_in = i := intervalContaining_unique iet x hx_in i hxs
      have hy_i : intervalContaining iet y hy_in = i := intervalContaining_unique iet y hy_in i hys
      rw [hx_i, hy_i]
      -- Now both map to rangeLeft (permutation i) + (· - domainLeft i)
      -- This is a translation, so dist is preserved
      simp only [Real.dist_eq]
      -- |((rangeLeft i + (x - domainLeft i)) - (rangeLeft i + (y - domainLeft i)))| = |x - y|
      congr 1
      ring
    · -- On Iio 0: the function is identity
      simp only [Set.mem_Iio] at hxs hys
      have hx_not : ¬(x ∈ Ico 0 1) := by simp [hxs]
      have hy_not : ¬(y ∈ Ico 0 1) := by simp [hys]
      simp only [hx_not, hy_not, dif_neg, not_false_eq_true]
    · -- On Ici 1: the function is identity
      simp only [Set.mem_Ici] at hxs hys
      have hx_not : ¬(x ∈ Ico 0 1) := by
        simp only [Set.mem_Ico, not_and]
        intro _
        linarith
      have hy_not : ¬(y ∈ Ico 0 1) := by
        simp only [Set.mem_Ico, not_and]
        intro _
        linarith
      simp only [hx_not, hy_not, dif_neg, not_false_eq_true]

/-- An IET is a finite piecewise isometry.

The partition has finitely many pieces: n intervals from the IET, plus 2 additional pieces
(Iio 0 and Ici 1) for extending to all of ℝ. -/
noncomputable def toFinitePiecewiseIsometry : FinitePiecewiseIsometry ℝ where
  toPiecewiseIsometry := iet.toPiecewiseIsometry
  partition_finite := by
    -- The partition is Set.range iet.interval ∪ {Iio 0, Ici 1}
    -- This is finite because:
    -- 1. Set.range iet.interval is finite (domain is Fin n)
    -- 2. {Iio 0, Ici 1} is finite (two elements)
    apply Set.Finite.union
    · exact Set.finite_range _
    · apply Set.Finite.insert
      exact Set.finite_singleton _

end IntervalExchangeTransformation

section StandardForm

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

end TwoIntervals

section GeneralProperties

variable {n : ℕ} (iet : IntervalExchangeTransformation n)


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

end GeneralProperties

section ErgodicTheory

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

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
