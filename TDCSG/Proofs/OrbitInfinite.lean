/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.RealDynamics
import TDCSG.Definitions.IET
import TDCSG.Proofs.Orbit
import TDCSG.Proofs.IET
import TDCSG.Proofs.Zeta5
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Function

/-!
# Orbit Infiniteness for GG5 IET

This file proves that the GG5-induced interval exchange transformation has an infinite orbit,
establishing that iterates are injective by showing displacements cannot sum to zero due to
irrationality properties of the golden ratio.

## Main results

- `displacement_sum_ne_zero`: Nontrivial combinations of IET displacements are nonzero
- `GG5_IET_maps_to_self`: The IET preserves the unit interval [0,1)
- `GG5_IET_iterates_injective`: IET iterates are injective on a chosen point
- `GG5_IET_has_infinite_orbit`: The GG5 IET has an infinite orbit

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Real Function Set RealDynamics
open TDCSG.Definitions

theorem GG5_domainLeft_0 : GG5_induced_IET.domainLeft 0 = 0 := by
  unfold IntervalExchangeTransformation.domainLeft
  simp

theorem GG5_domainLeft_1 : GG5_induced_IET.domainLeft 1 = length1 := by
  unfold IntervalExchangeTransformation.domainLeft GG5_induced_IET
  simp

theorem GG5_domainLeft_2 : GG5_induced_IET.domainLeft 2 = length1 + length2 := by
  unfold IntervalExchangeTransformation.domainLeft GG5_induced_IET
  simp [Fin.sum_univ_two]

theorem GG5_rangeLeft_0 : GG5_induced_IET.rangeLeft 0 = 0 := by
  unfold IntervalExchangeTransformation.rangeLeft
  simp

theorem GG5_rangeLeft_1 : GG5_induced_IET.rangeLeft 1 = length3 := by

  unfold IntervalExchangeTransformation.rangeLeft GG5_induced_IET

  have h_eq : (∑ x : Fin 1,
      if cyclicPerm3.symm ⟨↑x, Nat.lt_trans x.isLt (by omega : 1 < 3)⟩ = 0 then length1
      else if cyclicPerm3.symm ⟨↑x, Nat.lt_trans x.isLt (by omega : 1 < 3)⟩ = 1 then length2
      else length3) = length3 := by

    have hs : cyclicPerm3.symm ⟨0, by omega⟩ = (2 : Fin 3) := by unfold cyclicPerm3; native_decide
    simp only [Fin.sum_univ_one, Fin.val_zero, hs, Fin.reduceEq, ↓reduceIte]
  convert h_eq using 2

theorem GG5_rangeLeft_2 : GG5_induced_IET.rangeLeft 2 = length3 + length1 := by

  unfold IntervalExchangeTransformation.rangeLeft GG5_induced_IET
  have hs0 : cyclicPerm3.symm ⟨0, by omega⟩ = (2 : Fin 3) := by unfold cyclicPerm3; native_decide
  have hs1 : cyclicPerm3.symm ⟨1, by omega⟩ = (0 : Fin 3) := by unfold cyclicPerm3; native_decide
  have h_eq : (∑ x : Fin 2,
      if cyclicPerm3.symm ⟨↑x, Nat.lt_trans x.isLt (by omega : 2 < 3)⟩ = 0 then length1
      else if cyclicPerm3.symm ⟨↑x, Nat.lt_trans x.isLt (by omega : 2 < 3)⟩ = 1 then length2
      else length3) = length3 + length1 := by
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, hs0, hs1, Fin.reduceEq, ↓reduceIte]
  convert h_eq using 2

@[simp] theorem GG5_perm_0 : GG5_induced_IET.permutation 0 = 1 := by
  unfold GG5_induced_IET cyclicPerm3; decide

@[simp] theorem GG5_perm_1 : GG5_induced_IET.permutation 1 = 2 := by
  unfold GG5_induced_IET cyclicPerm3; decide

@[simp] theorem GG5_perm_2 : GG5_induced_IET.permutation 2 = 0 := by
  unfold GG5_induced_IET cyclicPerm3; decide

theorem GG5_actual_displacement_interval0 :
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) - GG5_induced_IET.domainLeft 0 = displacement0 := by
  simp only [GG5_perm_0, GG5_rangeLeft_1, GG5_domainLeft_0]

  unfold displacement0; ring

theorem GG5_actual_displacement_interval1 :
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 1) - GG5_induced_IET.domainLeft 1 = displacement1 := by
  simp only [GG5_perm_1, GG5_rangeLeft_2, GG5_domainLeft_1]

  unfold displacement1; ring

theorem GG5_actual_displacement_interval2 :
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 2) - GG5_induced_IET.domainLeft 2 = displacement2 := by
  simp only [GG5_perm_2, GG5_rangeLeft_0, GG5_domainLeft_2]

  unfold displacement2; ring

/-- Helper lemma: The IET toFun at a point in interval i equals the expected translation. -/
lemma IET_toFun_at_interval (i : Fin 3) (x : ℝ) (h_in_i : x ∈ GG5_induced_IET.interval i) :
    GG5_induced_IET.toFun x =
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i) := by
  unfold IntervalExchangeTransformation.toFun

  have h_ex : ∃ y, ∃ j, x ∈ GG5_induced_IET.interval j ∧
      y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) + (x - GG5_induced_IET.domainLeft j) := by
    use GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i), i

  have h_unique : ∀ y, (∃ j, x ∈ GG5_induced_IET.interval j ∧
      y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) + (x - GG5_induced_IET.domainLeft j)) →
      y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i) := by
    intro y ⟨j, hj_mem, hj_eq⟩
    have : j = i := by
      by_contra h_ne
      have h_disj := GG5_induced_IET.intervals_disjoint (Set.mem_range_self i) (Set.mem_range_self j)
                       (by intro heq; exact h_ne (GG5_induced_IET.interval_injective heq.symm))
      have : x ∈ GG5_induced_IET.interval i ∩ GG5_induced_IET.interval j := ⟨h_in_i, hj_mem⟩
      exact Set.disjoint_iff_inter_eq_empty.mp h_disj |>.subset this
    rw [this] at hj_eq
    exact hj_eq

  have h_eps : Classical.epsilon (fun y => ∃ j, x ∈ GG5_induced_IET.interval j ∧
      y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) + (x - GG5_induced_IET.domainLeft j)) =
      GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i) := by
    have h_spec := Classical.epsilon_spec h_ex
    exact h_unique _ h_spec

  exact h_eps

theorem GG5_displacement_eq_toFun_sub (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    GG5_displacement x = GG5_induced_IET.toFun x - x := by
  unfold GG5_displacement

  by_cases h0 : x < length1
  · simp only [h0, if_true]
    have h_in_0 : x ∈ GG5_induced_IET.interval 0 := by
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
      rw [GG5_domainLeft_0]
      simp only [GG5_induced_IET, Set.mem_Ico]
      exact ⟨hx.1, by simp; exact h0⟩
    rw [IET_toFun_at_interval 0 x h_in_0, GG5_domainLeft_0]
    have h := GG5_actual_displacement_interval0
    simp only [GG5_domainLeft_0, sub_zero] at h
    rw [← h]; ring
  · by_cases h1 : x < length1 + length2
    · simp only [h0, h1, if_false, if_true]
      have h_in_1 : x ∈ GG5_induced_IET.interval 1 := by
        unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
        rw [GG5_domainLeft_1]
        simp only [GG5_induced_IET, Set.mem_Ico]
        constructor
        · push_neg at h0; exact h0
        · simp; exact h1
      rw [IET_toFun_at_interval 1 x h_in_1, GG5_domainLeft_1]
      rw [← GG5_actual_displacement_interval1, GG5_domainLeft_1]
      ring
    · simp only [h0, h1, if_false]
      have h_in_2 : x ∈ GG5_induced_IET.interval 2 := by
        unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
        rw [GG5_domainLeft_2]
        simp only [GG5_induced_IET, Set.mem_Ico]
        constructor
        · push_neg at h1; exact h1
        · have h_sum := lengths_sum_to_one
          simp; linarith [hx.2]
      rw [IET_toFun_at_interval 2 x h_in_2, GG5_domainLeft_2]
      rw [← GG5_actual_displacement_interval2, GG5_domainLeft_2]
      ring

theorem cumulative_displacement_telescope (y : ℝ)
    (n : ℕ) (hn : ∀ k < n, (GG5_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1) :
    cumulative_displacement y n = (GG5_induced_IET.toFun^[n]) y - y := by
  induction n with
  | zero =>
    simp [cumulative_displacement]
  | succ k ih =>
    rw [cumulative_displacement, Finset.sum_range_succ]
    have hk : ∀ j < k, (GG5_induced_IET.toFun^[j]) y ∈ Set.Ico 0 1 := by
      intro j hj; exact hn j (Nat.lt_trans hj (Nat.lt_succ_self k))
    have h_fk_mem : (GG5_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1 := hn k (Nat.lt_succ_self k)
    rw [GG5_displacement_eq_toFun_sub _ h_fk_mem]
    simp only [cumulative_displacement] at ih
    rw [ih hk]
    simp only [Function.iterate_succ_apply']
    ring

theorem int_add_int_mul_phi_eq_zero (a b : ℤ)
    (h : (a : ℝ) + (b : ℝ) * goldenRatio = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  ·
    simp only [hb, Int.cast_zero, zero_mul, add_zero] at h
    have ha : a = 0 := by
      have : (a : ℝ) = 0 := h
      exact Int.cast_eq_zero.mp this
    exact ⟨ha, hb⟩
  ·
    exfalso
    have hφ : goldenRatio = -(a : ℝ) / b := by
      have hb_ne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
      field_simp at h ⊢
      linarith

    have : Irrational goldenRatio := goldenRatio_irrational
    apply this
    use ((-a : ℤ) : ℚ) / b
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    push_cast
    exact hφ.symm

theorem displacement_sum_ne_zero (n₀ n₁ n₂ : ℕ) (h_sum : 0 < n₀ + n₁ + n₂) :
    n₀ * displacement0 + n₁ * displacement1 + n₂ * displacement2 ≠ 0 := by
  intro h_zero

  rw [displacement0_formula, displacement1_formula, displacement2_formula] at h_zero

  have h_phi_pos : 0 < goldenRatio := goldenRatio_pos
  have h_phi_ne : goldenRatio ≠ 0 := ne_of_gt h_phi_pos
  have h_one_phi_pos : 0 < 1 + goldenRatio := by linarith
  have h_one_phi_ne : 1 + goldenRatio ≠ 0 := ne_of_gt h_one_phi_pos

  have h_clear : (n₀ + n₁ : ℝ) * (1 + goldenRatio) = (n₂ : ℝ) * goldenRatio := by

    have h_scaled : (n₀ : ℝ) * (1 + goldenRatio) + n₁ * (1 + goldenRatio) - n₂ * goldenRatio = 0 := by
      have h := h_zero
      calc (n₀ : ℝ) * (1 + goldenRatio) + n₁ * (1 + goldenRatio) - n₂ * goldenRatio
          = (n₀ * (1/goldenRatio) + n₁ * (1/goldenRatio) + n₂ * (-1/(1+goldenRatio))) *
            (goldenRatio * (1 + goldenRatio)) := by field_simp; ring
        _ = 0 * (goldenRatio * (1 + goldenRatio)) := by rw [h]
        _ = 0 := by ring
    linarith

  have h_coeff : ((n₀ : ℝ) + n₁) + ((n₀ : ℝ) + n₁ - n₂) * goldenRatio = 0 := by
    have h := h_clear
    ring_nf at h ⊢
    linarith

  have h_int := int_add_int_mul_phi_eq_zero ((n₀ : ℤ) + n₁) (n₀ + n₁ - n₂)
    (by push_cast; convert h_coeff using 1)

  have h1 : (n₀ : ℤ) + n₁ = 0 := h_int.1
  have h2 : (n₀ : ℤ) + n₁ - n₂ = 0 := h_int.2

  have hn0 : n₀ = 0 := by omega
  have hn1 : n₁ = 0 := by omega
  have hn2 : n₂ = 0 := by omega

  omega

theorem GG5_IET_maps_to_self :
    ∀ x ∈ Set.Ico 0 1, GG5_induced_IET.toFun x ∈ Set.Ico 0 1 := by
  intro x hx
  unfold IntervalExchangeTransformation.toFun

  have h_cover : x ∈ ⋃ i, GG5_induced_IET.interval i := by
    rw [GG5_induced_IET.intervals_cover]; exact hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h_cover

  have h_exists : ∃ y, ∃ j, x ∈ GG5_induced_IET.interval j ∧
      y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) + (x - GG5_induced_IET.domainLeft j) := by
    use GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i), i, hi
  suffices h_suff : ∀ y, (∃ j, x ∈ GG5_induced_IET.interval j ∧
      y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) + (x - GG5_induced_IET.domainLeft j)) →
      y ∈ Ico 0 1 by
    apply h_suff; exact Classical.epsilon_spec h_exists
  intro y ⟨j, hj_mem, hj_eq⟩
  rw [hj_eq]

  constructor
  ·
    have h_range_nn : 0 ≤ GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) := by
      unfold IntervalExchangeTransformation.rangeLeft
      apply Finset.sum_nonneg; intro k _; exact le_of_lt (GG5_induced_IET.lengths_pos _)
    have h_offset_nn : 0 ≤ x - GG5_induced_IET.domainLeft j := by
      unfold IntervalExchangeTransformation.interval at hj_mem; linarith [hj_mem.1]
    linarith
  ·
    have h_offset_lt : x - GG5_induced_IET.domainLeft j < GG5_induced_IET.lengths j := by
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight at hj_mem
      linarith [hj_mem.2]

    have h_bound : GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation j) + GG5_induced_IET.lengths j ≤ 1 := by
      fin_cases j
      ·
        show GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) + GG5_induced_IET.lengths 0 ≤ 1
        rw [GG5_perm_0, GG5_rangeLeft_1]
        simp only [GG5_induced_IET, ↓reduceIte]
        have h := lengths_sum_to_one; linarith [length2_pos]
      ·
        show GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 1) + GG5_induced_IET.lengths 1 ≤ 1
        rw [GG5_perm_1, GG5_rangeLeft_2]
        simp only [GG5_induced_IET, Fin.reduceEq, ↓reduceIte]
        have h := lengths_sum_to_one; linarith
      ·
        show GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 2) + GG5_induced_IET.lengths 2 ≤ 1
        rw [GG5_perm_2, GG5_rangeLeft_0]
        simp only [GG5_induced_IET, Fin.reduceEq, ↓reduceIte]
        have h := lengths_sum_to_one; linarith [length1_pos, length2_pos]
    linarith [h_bound, h_offset_lt]

theorem length1_half_mem_Ico : length1 / 2 ∈ Set.Ico 0 1 := by
  constructor
  · apply le_of_lt
    apply div_pos; exact length1_pos; norm_num
  · calc length1 / 2 = length1 * (1 / 2) := by ring
      _ < length1 * 1 := by
        apply mul_lt_mul_of_pos_left
        · norm_num
        · exact length1_pos
      _ = length1 := by ring
      _ < 1 := by
        have : length1 + length2 + length3 = 1 := lengths_sum_to_one
        linarith [length2_pos, length3_pos]

theorem GG5_IET_iterate_mem_Ico (n : ℕ) :
    (GG5_induced_IET.toFun^[n]) (length1 / 2) ∈ Set.Ico 0 1 := by
  induction n with
  | zero => simp; exact length1_half_mem_Ico
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    apply GG5_IET_maps_to_self
    exact ih

theorem GG5_IET_iterates_injective :
    Function.Injective (fun n : ℕ => (GG5_induced_IET.toFun^[n]) (length1 / 2)) := by

  intro m n hmn
  by_contra h_ne

  wlog h_lt : m < n generalizing m n with H
  · have h_gt : n < m := Nat.lt_of_le_of_ne (Nat.not_lt.mp h_lt) (Ne.symm h_ne)
    exact H hmn.symm (Ne.symm h_ne) h_gt

  have h_periodic : (GG5_induced_IET.toFun^[m]) (length1 / 2) ∈ Function.periodicPts GG5_induced_IET.toFun := by
    have h_period : 0 < n - m := Nat.sub_pos_of_lt h_lt
    have h_eq : (GG5_induced_IET.toFun^[n - m]) ((GG5_induced_IET.toFun^[m]) (length1 / 2)) =
                (GG5_induced_IET.toFun^[m]) (length1 / 2) := by
      calc (GG5_induced_IET.toFun^[n - m]) ((GG5_induced_IET.toFun^[m]) (length1 / 2))
          = (GG5_induced_IET.toFun^[n - m + m]) (length1 / 2) := by rw [Function.iterate_add_apply]
        _ = (GG5_induced_IET.toFun^[n]) (length1 / 2) := by congr 1; omega
        _ = (GG5_induced_IET.toFun^[m]) (length1 / 2) := hmn.symm
    exact Function.mk_mem_periodicPts h_period h_eq

  have h_mem : (GG5_induced_IET.toFun^[m]) (length1 / 2) ∈ Set.Ico 0 1 :=
    GG5_IET_iterate_mem_Ico m

  let p := Function.minimalPeriod GG5_induced_IET.toFun ((GG5_induced_IET.toFun^[m]) (length1 / 2))
  have hp_pos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts h_periodic

  have h_return : (GG5_induced_IET.toFun^[p]) ((GG5_induced_IET.toFun^[m]) (length1 / 2)) =
                  (GG5_induced_IET.toFun^[m]) (length1 / 2) :=
    Function.isPeriodicPt_minimalPeriod _ _

  exfalso

  let y := (GG5_induced_IET.toFun^[m]) (length1 / 2)

  have h_iter_mem : ∀ k < p, (GG5_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1 := by
    intro k _

    have h_eq : (GG5_induced_IET.toFun^[k]) y = (GG5_induced_IET.toFun^[k + m]) (length1 / 2) := by
      calc (GG5_induced_IET.toFun^[k]) y
          = (GG5_induced_IET.toFun^[k]) ((GG5_induced_IET.toFun^[m]) (length1 / 2)) := rfl
        _ = (GG5_induced_IET.toFun^[k + m]) (length1 / 2) := by rw [Function.iterate_add_apply]
    rw [h_eq]
    exact GG5_IET_iterate_mem_Ico (k + m)

  have h_cum_zero : cumulative_displacement y p = 0 := by
    rw [cumulative_displacement_telescope y p h_iter_mem, h_return, sub_self]

  let visits_0 := Finset.filter (fun k => (GG5_induced_IET.toFun^[k]) y < length1) (Finset.range p)
  let visits_1 := Finset.filter (fun k => length1 ≤ (GG5_induced_IET.toFun^[k]) y ∧
                                          (GG5_induced_IET.toFun^[k]) y < length1 + length2) (Finset.range p)
  let visits_2 := Finset.filter (fun k => length1 + length2 ≤ (GG5_induced_IET.toFun^[k]) y) (Finset.range p)

  have h_cum_expand : cumulative_displacement y p =
      ∑ k ∈ Finset.range p, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) := rfl

  have h_disp_cases : ∀ k ∈ Finset.range p,
      GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
        if (GG5_induced_IET.toFun^[k]) y < length1 then displacement0
        else if (GG5_induced_IET.toFun^[k]) y < length1 + length2 then displacement1
        else displacement2 := by
    intro k _
    rfl

  have h_partition : Finset.range p = visits_0 ∪ visits_1 ∪ visits_2 := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, visits_0, visits_1, visits_2]
    constructor
    · intro hk
      by_cases h0 : (GG5_induced_IET.toFun^[k]) y < length1
      · left; left; exact ⟨hk, h0⟩
      · by_cases h1 : (GG5_induced_IET.toFun^[k]) y < length1 + length2
        · left; right
          push_neg at h0
          exact ⟨hk, h0, h1⟩
        · right
          push_neg at h1
          exact ⟨hk, h1⟩
    · intro h
      rcases h with ((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk

  have h_disjoint_01 : Disjoint visits_0 visits_1 := by
    simp only [Finset.disjoint_iff_ne, visits_0, visits_1, Finset.mem_filter]
    intro a ⟨_, ha0⟩ b ⟨_, hb1, _⟩ hab
    rw [hab] at ha0
    linarith

  have h_disjoint_02 : Disjoint visits_0 visits_2 := by
    simp only [Finset.disjoint_iff_ne, visits_0, visits_2, Finset.mem_filter]
    intro a ⟨_, ha0⟩ b ⟨_, hb2⟩ hab
    subst hab

    linarith [length2_pos]

  have h_disjoint_12 : Disjoint visits_1 visits_2 := by
    simp only [Finset.disjoint_iff_ne, visits_1, visits_2, Finset.mem_filter]
    intro a ⟨_, _, ha1⟩ b ⟨_, hb2⟩ hab
    rw [hab] at ha1
    linarith

  have h_sum_split : ∑ k ∈ Finset.range p, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
      ∑ k ∈ visits_0, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) +
      ∑ k ∈ visits_1, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) +
      ∑ k ∈ visits_2, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) := by
    rw [h_partition]

    have h_disjoint_01_2 : Disjoint (visits_0 ∪ visits_1) visits_2 :=
      Finset.disjoint_union_left.mpr ⟨h_disjoint_02, h_disjoint_12⟩
    rw [Finset.sum_union h_disjoint_01_2, Finset.sum_union h_disjoint_01]

  have h_sum_0 : ∑ k ∈ visits_0, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
                 visits_0.card * displacement0 := by
    have h_all_eq : ∀ k ∈ visits_0, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) = displacement0 := by
      intro k hk
      simp only [Finset.mem_filter, visits_0] at hk
      unfold GG5_displacement
      simp [hk.2]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  have h_sum_1 : ∑ k ∈ visits_1, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
                 visits_1.card * displacement1 := by
    have h_all_eq : ∀ k ∈ visits_1, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) = displacement1 := by
      intro k hk
      simp only [Finset.mem_filter, visits_1] at hk
      unfold GG5_displacement
      have h_not_0 : ¬ (GG5_induced_IET.toFun^[k]) y < length1 := by linarith [hk.2.1]
      simp [h_not_0, hk.2.2]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  have h_sum_2 : ∑ k ∈ visits_2, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
                 visits_2.card * displacement2 := by
    have h_all_eq : ∀ k ∈ visits_2, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) = displacement2 := by
      intro k hk
      simp only [Finset.mem_filter, visits_2] at hk
      unfold GG5_displacement
      have h_not_0 : ¬ (GG5_induced_IET.toFun^[k]) y < length1 := by
        linarith [hk.2, length2_pos]
      have h_not_1 : ¬ (GG5_induced_IET.toFun^[k]) y < length1 + length2 := by linarith [hk.2]
      simp [h_not_0, h_not_1]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  have h_cum_as_sum : cumulative_displacement y p =
      visits_0.card * displacement0 + visits_1.card * displacement1 + visits_2.card * displacement2 := by
    rw [h_cum_expand, h_sum_split, h_sum_0, h_sum_1, h_sum_2]

  have h_card_sum : visits_0.card + visits_1.card + visits_2.card = p := by
    have h_disj1 : Disjoint visits_0 (visits_1 ∪ visits_2) :=
      Finset.disjoint_union_right.mpr ⟨h_disjoint_01, h_disjoint_02⟩
    have h_disj2 : Disjoint visits_1 visits_2 := h_disjoint_12
    calc visits_0.card + visits_1.card + visits_2.card
        = visits_0.card + (visits_1.card + visits_2.card) := by ring
      _ = visits_0.card + (visits_1 ∪ visits_2).card := by
          rw [Finset.card_union_of_disjoint h_disj2]
      _ = (visits_0 ∪ (visits_1 ∪ visits_2)).card := by
          rw [Finset.card_union_of_disjoint h_disj1]
      _ = (visits_0 ∪ visits_1 ∪ visits_2).card := by
          rw [Finset.union_assoc]
      _ = (Finset.range p).card := by rw [← h_partition]
      _ = p := Finset.card_range p

  have h_sum_pos : 0 < visits_0.card + visits_1.card + visits_2.card := by
    rw [h_card_sum]; exact hp_pos

  have h_ne_zero := displacement_sum_ne_zero visits_0.card visits_1.card visits_2.card h_sum_pos

  rw [h_cum_as_sum] at h_cum_zero
  exact h_ne_zero h_cum_zero

theorem GG5_IET_has_infinite_orbit :
    ∃ (x : ℝ), x ∈ Set.Ico 0 1 ∧
      (RealDynamics.orbitSet GG5_induced_IET.toFun x).Infinite := by
  use length1 / 2
  constructor
  · exact length1_half_mem_Ico
  ·
    apply Set.infinite_of_injective_forall_mem GG5_IET_iterates_injective
    intro n
    exact RealDynamics.orbitSet_iterate _ _ n

end TDCSG.CompoundSymmetry.GG5
