/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.GG10.IET
import TDCSG.Definitions.RealDynamics
import TDCSG.Proofs.IET
import TDCSG.Proofs.Orbit
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Function

/-!
# Orbit Infiniteness for GG10 IET

This file proves that the GG10-induced 2-interval exchange transformation has infinite orbits,
establishing that iterates are injective by showing displacements cannot sum to zero due to
irrationality properties of the golden ratio.

## Main results

- `displacement10_sum_ne_zero`: Nontrivial combinations of 2-IET displacements are nonzero
- `GG10_IET_maps_to_self`: The IET preserves the unit interval [0,1)
- `GG10_IET_iterates_injective`: IET iterates are injective on a chosen point
- `GG10_IET_has_infinite_orbit`: The GG10 IET has an infinite orbit

## Key difference from GG5

The GG10 case is simpler than GG5 because:
1. It uses a 2-interval IET (swap) instead of 3-interval (cyclic permutation)
2. The two displacements are +(2-φ) and -1/φ, which sum to 0 for one application of each
3. But since (2-φ)/(1/φ) = φ is irrational, no combination n₀(2-φ) + n₁(-1/φ) = 0 except n₀=n₁

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.GG10

open Real Function Set RealDynamics
open TDCSG.Definitions

/-! ### Displacement Function -/

/-- The displacement function for the GG10 interval exchange transformation.

This piecewise constant function assigns a translation amount to each of the two
intervals that partition [0, 1]:
- On [0, 1/φ): displacement by `displacement1_10` = 2-φ ≈ +0.382
- On [1/φ, 1): displacement by `displacement2_10` = -1/φ ≈ -0.618

The key property is that (2-φ)/(1/φ) = φ(2-φ) = 2φ - φ² = 2φ - (φ+1) = φ - 1 = 1/φ,
so the ratio is φ, which is irrational. -/
noncomputable def GG10_displacement (x : ℝ) : ℝ :=
  if x < length1_10 then displacement1_10
  else displacement2_10

/-- Cumulative displacement after `n` iterations of the GG10 IET.

Computes the total signed displacement accumulated by starting at point `y` and applying
the IET `n` times, summing the displacement at each step. -/
noncomputable def cumulative_displacement_10 (y : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, GG10_displacement ((GG10_induced_IET.toFun^[k]) y)

/-! ### Domain and Range Calculations -/

/-- The left endpoint of interval 0 in the GG10 IET is 0. -/
theorem GG10_domainLeft_0 : GG10_induced_IET.domainLeft 0 = 0 := by
  unfold IntervalExchangeTransformation.domainLeft
  simp

/-- The left endpoint of interval 1 equals `length1_10`. -/
theorem GG10_domainLeft_1 : GG10_induced_IET.domainLeft 1 = length1_10 := by
  unfold IntervalExchangeTransformation.domainLeft GG10_induced_IET
  simp

/-- The left endpoint of range interval 0 is 0. -/
theorem GG10_rangeLeft_0 : GG10_induced_IET.rangeLeft 0 = 0 := by
  unfold IntervalExchangeTransformation.rangeLeft
  simp

/-- The left endpoint of range interval 1 equals `length2_10` (the swap permutation
    places interval 1 first in the range). -/
theorem GG10_rangeLeft_1 : GG10_induced_IET.rangeLeft 1 = length2_10 := by
  unfold IntervalExchangeTransformation.rangeLeft GG10_induced_IET
  have h_eq : (∑ x : Fin 1,
      if swapPerm2.symm ⟨↑x, Nat.lt_trans x.isLt (by omega : 1 < 2)⟩ = 0 then length1_10
      else length2_10) = length2_10 := by
    have hs : swapPerm2.symm ⟨0, by omega⟩ = (1 : Fin 2) := by unfold swapPerm2; native_decide
    simp only [Fin.sum_univ_one, Fin.val_zero, hs, Fin.reduceEq, ↓reduceIte]
  convert h_eq using 2

/-! ### Permutation Properties -/

/-- The GG10 swap permutation sends interval 0 to position 1. -/
@[simp] theorem GG10_perm_0 : GG10_induced_IET.permutation 0 = 1 := by
  unfold GG10_induced_IET swapPerm2; decide

/-- The GG10 swap permutation sends interval 1 to position 0. -/
@[simp] theorem GG10_perm_1 : GG10_induced_IET.permutation 1 = 0 := by
  unfold GG10_induced_IET swapPerm2; decide

/-! ### Displacement Verification -/

/-- The displacement for interval 0: points in [0, 1/φ) are translated by 2-φ. -/
theorem GG10_actual_displacement_interval0 :
    GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation 0) - GG10_induced_IET.domainLeft 0 = displacement1_10 := by
  simp only [GG10_perm_0, GG10_rangeLeft_1, GG10_domainLeft_0]
  unfold displacement1_10 length2_10
  -- Need to show: 1 - 1/φ = 2 - φ
  -- Using φ² = φ + 1, we have 1/φ = φ - 1, so 1 - 1/φ = 1 - (φ - 1) = 2 - φ
  have hφ_pos : 0 < goldenRatio := goldenRatio_pos
  have hφ_ne : goldenRatio ≠ 0 := ne_of_gt hφ_pos
  have h_inv_phi : 1 / φ = φ - 1 := by
    have h := goldenRatio_sq
    have hsq : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    field_simp
    nlinarith [hsq, sq_nonneg (sqrt 5)]
  simp only [sub_zero]
  rw [h_inv_phi]
  ring

/-- The displacement for interval 1: points in [1/φ, 1) are translated by -1/φ. -/
theorem GG10_actual_displacement_interval1 :
    GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation 1) - GG10_induced_IET.domainLeft 1 = displacement2_10 := by
  simp only [GG10_perm_1, GG10_rangeLeft_0, GG10_domainLeft_1]
  unfold displacement2_10 length1_10
  ring

/-! ### IET Evaluation -/

/-- For a point in interval `i`, the IET evaluates to the range-left of the permuted interval
    plus the offset within the original interval. -/
lemma IET10_toFun_at_interval (i : Fin 2) (x : ℝ) (h_in_i : x ∈ GG10_induced_IET.interval i) :
    GG10_induced_IET.toFun x =
    GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation i) + (x - GG10_induced_IET.domainLeft i) := by
  unfold IntervalExchangeTransformation.toFun
  have h_ex : ∃ y, ∃ j, x ∈ GG10_induced_IET.interval j ∧
      y = GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) + (x - GG10_induced_IET.domainLeft j) := by
    use GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation i) + (x - GG10_induced_IET.domainLeft i), i
  have h_unique : ∀ y, (∃ j, x ∈ GG10_induced_IET.interval j ∧
      y = GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) + (x - GG10_induced_IET.domainLeft j)) →
      y = GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation i) + (x - GG10_induced_IET.domainLeft i) := by
    intro y ⟨j, hj_mem, hj_eq⟩
    have : j = i := by
      by_contra h_ne
      have h_disj := GG10_induced_IET.intervals_disjoint (Set.mem_range_self i) (Set.mem_range_self j)
                       (by intro heq; exact h_ne (GG10_induced_IET.interval_injective heq.symm))
      have : x ∈ GG10_induced_IET.interval i ∩ GG10_induced_IET.interval j := ⟨h_in_i, hj_mem⟩
      exact Set.disjoint_iff_inter_eq_empty.mp h_disj |>.subset this
    rw [this] at hj_eq
    exact hj_eq
  have h_eps : Classical.epsilon (fun y => ∃ j, x ∈ GG10_induced_IET.interval j ∧
      y = GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) + (x - GG10_induced_IET.domainLeft j)) =
      GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation i) + (x - GG10_induced_IET.domainLeft i) := by
    have h_spec := Classical.epsilon_spec h_ex
    exact h_unique _ h_spec
  exact h_eps

/-- The symbolic displacement function equals the actual IET translation. -/
theorem GG10_displacement_eq_toFun_sub (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    GG10_displacement x = GG10_induced_IET.toFun x - x := by
  unfold GG10_displacement
  by_cases h0 : x < length1_10
  · simp only [h0, if_true]
    have h_in_0 : x ∈ GG10_induced_IET.interval 0 := by
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
      rw [GG10_domainLeft_0]
      simp only [GG10_induced_IET, Set.mem_Ico]
      exact ⟨hx.1, by simp; exact h0⟩
    rw [IET10_toFun_at_interval 0 x h_in_0, GG10_domainLeft_0]
    have h := GG10_actual_displacement_interval0
    simp only [GG10_domainLeft_0, sub_zero] at h
    rw [← h]; ring
  · simp only [h0, if_false]
    have h_in_1 : x ∈ GG10_induced_IET.interval 1 := by
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
      rw [GG10_domainLeft_1]
      simp only [GG10_induced_IET, Set.mem_Ico]
      constructor
      · push_neg at h0; exact h0
      · simp; linarith [hx.2, lengths_sum_to_one_10]
    rw [IET10_toFun_at_interval 1 x h_in_1, GG10_domainLeft_1]
    rw [← GG10_actual_displacement_interval1, GG10_domainLeft_1]
    ring

/-! ### Cumulative Displacement -/

/-- The cumulative displacement after `n` iterations telescopes to `f^n(y) - y`. -/
theorem cumulative_displacement10_telescope (y : ℝ)
    (n : ℕ) (hn : ∀ k < n, (GG10_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1) :
    cumulative_displacement_10 y n = (GG10_induced_IET.toFun^[n]) y - y := by
  induction n with
  | zero =>
    simp [cumulative_displacement_10]
  | succ k ih =>
    rw [cumulative_displacement_10, Finset.sum_range_succ]
    have hk : ∀ j < k, (GG10_induced_IET.toFun^[j]) y ∈ Set.Ico 0 1 := by
      intro j hj; exact hn j (Nat.lt_trans hj (Nat.lt_succ_self k))
    have h_fk_mem : (GG10_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1 := hn k (Nat.lt_succ_self k)
    rw [GG10_displacement_eq_toFun_sub _ h_fk_mem]
    simp only [cumulative_displacement_10] at ih
    rw [ih hk]
    simp only [Function.iterate_succ_apply']
    ring

/-! ### Irrationality Argument -/

/-- Any nontrivial combination of the two IET displacements is nonzero.

The displacements are 2-φ = 1/φ² and -1/φ. If n₀(1/φ²) + n₁(-1/φ) = 0, then
multiplying by φ² gives n₀ - n₁φ = 0. Since φ is irrational and n₀, n₁ are
natural numbers, this forces n₀ = n₁ = 0. -/
theorem displacement10_sum_ne_zero (n₀ n₁ : ℕ) (h_sum : 0 < n₀ + n₁) :
    n₀ * displacement1_10 + n₁ * displacement2_10 ≠ 0 := by
  intro h_zero
  unfold displacement1_10 displacement2_10 at h_zero
  -- h_zero: n₀ * (2 - φ) + n₁ * (-(1/φ)) = 0
  -- Rearranging: n₀ * (2 - φ) = n₁ * (1/φ)
  have hφ_pos : 0 < goldenRatio := goldenRatio_pos
  have hφ_ne : goldenRatio ≠ 0 := ne_of_gt hφ_pos
  -- Use 2 - φ = 1/φ² and simplify
  have h_two_minus_phi : (2 : ℝ) - φ = 1 / φ^2 := two_minus_phi_eq
  rw [h_two_minus_phi] at h_zero
  -- Now: n₀ * (1/φ²) - n₁ * (1/φ) = 0
  -- Multiply by φ²: n₀ - n₁ * φ = 0
  have h_scaled : (n₀ : ℝ) - n₁ * φ = 0 := by
    have h := h_zero
    have hφ2_ne : φ^2 ≠ 0 := pow_ne_zero 2 hφ_ne
    calc (n₀ : ℝ) - n₁ * φ
        = (n₀ * (1/φ^2) + n₁ * (-(1/φ))) * φ^2 := by field_simp; ring
      _ = 0 * φ^2 := by rw [h]
      _ = 0 := by ring
  -- So n₀ = n₁ * φ, which is impossible for integers unless both are 0
  have h_eq : (n₀ : ℝ) = n₁ * φ := by linarith
  by_cases hn1 : n₁ = 0
  · simp only [hn1, Nat.cast_zero, zero_mul] at h_eq
    have hn0 : n₀ = 0 := Nat.cast_eq_zero.mp h_eq
    omega
  · exfalso
    have hφ_eq : goldenRatio = (n₀ : ℝ) / n₁ := by
      have hn1_ne : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn1
      field_simp [hn1_ne] at h_eq ⊢
      linarith
    have : Irrational goldenRatio := goldenRatio_irrational
    apply this
    use (n₀ : ℚ) / n₁
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
    exact hφ_eq.symm

/-! ### IET Self-Mapping -/

/-- The GG10 IET preserves the unit interval [0, 1). -/
theorem GG10_IET_maps_to_self :
    ∀ x ∈ Set.Ico 0 1, GG10_induced_IET.toFun x ∈ Set.Ico 0 1 := by
  intro x hx
  unfold IntervalExchangeTransformation.toFun
  have h_cover : x ∈ ⋃ i, GG10_induced_IET.interval i := by
    rw [GG10_induced_IET.intervals_cover]; exact hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h_cover
  have h_exists : ∃ y, ∃ j, x ∈ GG10_induced_IET.interval j ∧
      y = GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) + (x - GG10_induced_IET.domainLeft j) := by
    use GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation i) + (x - GG10_induced_IET.domainLeft i), i, hi
  suffices h_suff : ∀ y, (∃ j, x ∈ GG10_induced_IET.interval j ∧
      y = GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) + (x - GG10_induced_IET.domainLeft j)) →
      y ∈ Ico 0 1 by
    apply h_suff; exact Classical.epsilon_spec h_exists
  intro y ⟨j, hj_mem, hj_eq⟩
  rw [hj_eq]
  constructor
  · have h_range_nn : 0 ≤ GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) := by
      unfold IntervalExchangeTransformation.rangeLeft
      apply Finset.sum_nonneg; intro k _; exact le_of_lt (GG10_induced_IET.lengths_pos _)
    have h_offset_nn : 0 ≤ x - GG10_induced_IET.domainLeft j := by
      unfold IntervalExchangeTransformation.interval at hj_mem; linarith [hj_mem.1]
    linarith
  · have h_offset_lt : x - GG10_induced_IET.domainLeft j < GG10_induced_IET.lengths j := by
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight at hj_mem
      linarith [hj_mem.2]
    have h_bound : GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation j) + GG10_induced_IET.lengths j ≤ 1 := by
      fin_cases j
      · show GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation 0) + GG10_induced_IET.lengths 0 ≤ 1
        rw [GG10_perm_0, GG10_rangeLeft_1]
        simp only [GG10_induced_IET, ↓reduceIte]
        have h := lengths_sum_to_one_10; linarith
      · show GG10_induced_IET.rangeLeft (GG10_induced_IET.permutation 1) + GG10_induced_IET.lengths 1 ≤ 1
        rw [GG10_perm_1, GG10_rangeLeft_0]
        simp only [GG10_induced_IET, Fin.reduceEq, ↓reduceIte]
        have h := lengths_sum_to_one_10; linarith [length1_10_pos]
    linarith [h_bound, h_offset_lt]

/-! ### Witness Point -/

/-- The midpoint of the first interval lies in [0, 1). -/
theorem length1_10_half_mem_Ico : length1_10 / 2 ∈ Set.Ico 0 1 := by
  constructor
  · apply le_of_lt
    apply div_pos; exact length1_10_pos; norm_num
  · calc length1_10 / 2 = length1_10 * (1 / 2) := by ring
      _ < length1_10 * 1 := by
        apply mul_lt_mul_of_pos_left
        · norm_num
        · exact length1_10_pos
      _ = length1_10 := by ring
      _ < 1 := by
        have : length1_10 + length2_10 = 1 := lengths_sum_to_one_10
        linarith [length2_10_pos]

/-- All iterates of the witness point remain in [0, 1). -/
theorem GG10_IET_iterate_mem_Ico (n : ℕ) :
    (GG10_induced_IET.toFun^[n]) (length1_10 / 2) ∈ Set.Ico 0 1 := by
  induction n with
  | zero => simp; exact length1_10_half_mem_Ico
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    apply GG10_IET_maps_to_self
    exact ih

/-! ### Main Theorems -/

/-- The map `n -> f^n(x0)` is injective, where `x0 = length1_10/2`.

This is the key technical lemma: distinct iteration counts produce distinct points.
The proof proceeds by contradiction: if `f^m(x0) = f^n(x0)` for `m < n`, then
the point `f^m(x0)` is periodic. But the cumulative displacement over the period
must be zero, which by `displacement10_sum_ne_zero` is impossible. -/
theorem GG10_IET_iterates_injective :
    Function.Injective (fun n : ℕ => (GG10_induced_IET.toFun^[n]) (length1_10 / 2)) := by
  intro m n hmn
  by_contra h_ne
  wlog h_lt : m < n generalizing m n with H
  · have h_gt : n < m := Nat.lt_of_le_of_ne (Nat.not_lt.mp h_lt) (Ne.symm h_ne)
    exact H hmn.symm (Ne.symm h_ne) h_gt

  have h_periodic : (GG10_induced_IET.toFun^[m]) (length1_10 / 2) ∈ Function.periodicPts GG10_induced_IET.toFun := by
    have h_period : 0 < n - m := Nat.sub_pos_of_lt h_lt
    have h_eq : (GG10_induced_IET.toFun^[n - m]) ((GG10_induced_IET.toFun^[m]) (length1_10 / 2)) =
                (GG10_induced_IET.toFun^[m]) (length1_10 / 2) := by
      calc (GG10_induced_IET.toFun^[n - m]) ((GG10_induced_IET.toFun^[m]) (length1_10 / 2))
          = (GG10_induced_IET.toFun^[n - m + m]) (length1_10 / 2) := by rw [Function.iterate_add_apply]
        _ = (GG10_induced_IET.toFun^[n]) (length1_10 / 2) := by congr 1; omega
        _ = (GG10_induced_IET.toFun^[m]) (length1_10 / 2) := hmn.symm
    exact Function.mk_mem_periodicPts h_period h_eq

  have h_mem : (GG10_induced_IET.toFun^[m]) (length1_10 / 2) ∈ Set.Ico 0 1 :=
    GG10_IET_iterate_mem_Ico m

  let p := Function.minimalPeriod GG10_induced_IET.toFun ((GG10_induced_IET.toFun^[m]) (length1_10 / 2))
  have hp_pos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts h_periodic

  have h_return : (GG10_induced_IET.toFun^[p]) ((GG10_induced_IET.toFun^[m]) (length1_10 / 2)) =
                  (GG10_induced_IET.toFun^[m]) (length1_10 / 2) :=
    Function.isPeriodicPt_minimalPeriod _ _

  exfalso

  let y := (GG10_induced_IET.toFun^[m]) (length1_10 / 2)

  have h_iter_mem : ∀ k < p, (GG10_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1 := by
    intro k _
    have h_eq : (GG10_induced_IET.toFun^[k]) y = (GG10_induced_IET.toFun^[k + m]) (length1_10 / 2) := by
      calc (GG10_induced_IET.toFun^[k]) y
          = (GG10_induced_IET.toFun^[k]) ((GG10_induced_IET.toFun^[m]) (length1_10 / 2)) := rfl
        _ = (GG10_induced_IET.toFun^[k + m]) (length1_10 / 2) := by rw [Function.iterate_add_apply]
    rw [h_eq]
    exact GG10_IET_iterate_mem_Ico (k + m)

  have h_cum_zero : cumulative_displacement_10 y p = 0 := by
    rw [cumulative_displacement10_telescope y p h_iter_mem, h_return, sub_self]

  -- Partition iterations by which interval they land in
  let visits_0 := Finset.filter (fun k => (GG10_induced_IET.toFun^[k]) y < length1_10) (Finset.range p)
  let visits_1 := Finset.filter (fun k => length1_10 ≤ (GG10_induced_IET.toFun^[k]) y) (Finset.range p)

  have h_cum_expand : cumulative_displacement_10 y p =
      ∑ k ∈ Finset.range p, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) := rfl

  have h_partition : Finset.range p = visits_0 ∪ visits_1 := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, visits_0, visits_1]
    constructor
    · intro hk
      by_cases h0 : (GG10_induced_IET.toFun^[k]) y < length1_10
      · left; exact ⟨hk, h0⟩
      · right; push_neg at h0; exact ⟨hk, h0⟩
    · intro h
      rcases h with (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk

  have h_disjoint : Disjoint visits_0 visits_1 := by
    simp only [Finset.disjoint_iff_ne, visits_0, visits_1, Finset.mem_filter]
    intro a ⟨_, ha0⟩ b ⟨_, hb1⟩ hab
    rw [hab] at ha0
    linarith

  have h_sum_split : ∑ k ∈ Finset.range p, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) =
      ∑ k ∈ visits_0, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) +
      ∑ k ∈ visits_1, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) := by
    rw [h_partition, Finset.sum_union h_disjoint]

  have h_sum_0 : ∑ k ∈ visits_0, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) =
                 visits_0.card * displacement1_10 := by
    have h_all_eq : ∀ k ∈ visits_0, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) = displacement1_10 := by
      intro k hk
      simp only [Finset.mem_filter, visits_0] at hk
      unfold GG10_displacement
      simp [hk.2]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  have h_sum_1 : ∑ k ∈ visits_1, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) =
                 visits_1.card * displacement2_10 := by
    have h_all_eq : ∀ k ∈ visits_1, GG10_displacement ((GG10_induced_IET.toFun^[k]) y) = displacement2_10 := by
      intro k hk
      simp only [Finset.mem_filter, visits_1] at hk
      unfold GG10_displacement
      have h_not_0 : ¬ (GG10_induced_IET.toFun^[k]) y < length1_10 := by linarith [hk.2]
      simp [h_not_0]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  have h_cum_as_sum : cumulative_displacement_10 y p =
      visits_0.card * displacement1_10 + visits_1.card * displacement2_10 := by
    rw [h_cum_expand, h_sum_split, h_sum_0, h_sum_1]

  have h_card_sum : visits_0.card + visits_1.card = p := by
    calc visits_0.card + visits_1.card
        = (visits_0 ∪ visits_1).card := by rw [Finset.card_union_of_disjoint h_disjoint]
      _ = (Finset.range p).card := by rw [← h_partition]
      _ = p := Finset.card_range p

  have h_sum_pos : 0 < visits_0.card + visits_1.card := by
    rw [h_card_sum]; exact hp_pos

  have h_ne_zero := displacement10_sum_ne_zero visits_0.card visits_1.card h_sum_pos

  rw [h_cum_as_sum] at h_cum_zero
  exact h_ne_zero h_cum_zero

/-- The GG10-induced IET has a point with infinite orbit.

This is the main result of this file, directly supporting the paper's theorem
("GG10 is infinite at r = sqrt(4 - phi)"). The interval exchange transformation
induced by the GG10 geometry at critical radius has the property that any point
in the interior generates infinitely many distinct images under iteration.

The proof exhibits `length1_10/2` as a witness: since distinct iteration counts
produce distinct points (`GG10_IET_iterates_injective`), the orbit must be infinite. -/
theorem GG10_IET_has_infinite_orbit :
    ∃ (x : ℝ), x ∈ Set.Ico 0 1 ∧
      (RealDynamics.orbitSet GG10_induced_IET.toFun x).Infinite := by
  use length1_10 / 2
  constructor
  · exact length1_10_half_mem_Ico
  · apply Set.infinite_of_injective_forall_mem GG10_IET_iterates_injective
    intro n
    exact RealDynamics.orbitSet_iterate _ _ n

end TDCSG.GG10
