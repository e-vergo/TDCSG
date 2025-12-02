/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.RealDynamics
import TDCSG.Proofs.IET

/-!
# Orbit Theory for Real Dynamical Systems

This file develops the theory of orbits for discrete real dynamical systems, proving that
finite orbits imply periodic points and that absence of periodic points implies infinite orbits.

## Main results

- `finite_orbit_has_collision`: Finite orbits contain repeated iterates
- `finite_orbit_implies_periodic`: Finite orbits contain periodic points
- `no_orbit_point_periodic_implies_infinite`: Orbits without periodic points are infinite
- `hasInfiniteOrbit_iff_orbitSet_infinite`: Characterization of infinite orbits

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace RealDynamics

open Function Set

theorem mem_orbitSet_self (f : ℝ → ℝ) (x : ℝ) : x ∈ orbitSet f x := by
  use 0
  simp

theorem mem_orbitSet_of_iterate (f : ℝ → ℝ) (x y : ℝ) (n : ℕ) (h : (f^[n]) x = y) :
    y ∈ orbitSet f x :=
  ⟨n, h⟩

theorem orbitSet_iterate (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    (f^[n]) x ∈ orbitSet f x :=
  ⟨n, rfl⟩

theorem finite_orbit_has_collision (f : ℝ → ℝ) (x : ℝ) (h_fin : (orbitSet f x).Finite) :
    ∃ (i j : ℕ), i < j ∧ (f^[i]) x = (f^[j]) x := by

  obtain ⟨s, hs⟩ := Set.Finite.exists_finset_coe h_fin
  let n := s.card

  have h_all_in_s : ∀ k ≤ n, (f^[k]) x ∈ s := by
    intro k _
    have : (f^[k]) x ∈ orbitSet f x := orbitSet_iterate f x k
    rw [← hs] at this
    exact this

  by_contra h_no_collision
  push_neg at h_no_collision

  have h_all_distinct : ∀ i j, i ≤ n → j ≤ n → i ≠ j → (f^[i]) x ≠ (f^[j]) x := by
    intro i j hi hj hij
    by_cases h : i < j
    · intro heq
      exact h_no_collision i j h heq
    · intro heq
      push_neg at h
      have hji : j < i := Nat.lt_of_le_of_ne h (Ne.symm hij)
      exact h_no_collision j i hji heq.symm

  have h_image_size : (Finset.image (fun k : Fin (n+1) => (f^[k.val]) x) Finset.univ).card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp at heq
      by_contra hij_ne
      simp at hij_ne
      have : (f^[i]) x ≠ (f^[j]) x :=
        h_all_distinct i j (Nat.lt_succ_iff.mp hi) (Nat.lt_succ_iff.mp hj) hij_ne
      exact this heq
  have h_image_subset : Finset.image (fun k : Fin (n+1) => (f^[k.val]) x) Finset.univ ⊆ s := by
    intro y hy
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hy
    rw [← hk]
    exact h_all_in_s k.val (Nat.lt_succ_iff.mp k.isLt)
  have : (Finset.image (fun k : Fin (n+1) => (f^[k.val]) x) Finset.univ).card ≤ s.card :=
    Finset.card_le_card h_image_subset
  omega

theorem finite_orbit_implies_periodic (f : ℝ → ℝ) (x : ℝ)
    (h_fin : (orbitSet f x).Finite) :
    ∃ (i k : ℕ), k > 0 ∧ (f^[i + k]) x = (f^[i]) x := by
  obtain ⟨i, j, hij, heq⟩ := finite_orbit_has_collision f x h_fin
  use i, j - i
  constructor
  · omega
  · calc (f^[i + (j - i)]) x = (f^[j]) x := by congr 1; omega
      _ = (f^[i]) x := heq.symm

theorem finite_orbit_has_periodic_point (f : ℝ → ℝ) (x : ℝ)
    (h_fin : (orbitSet f x).Finite) :
    ∃ (m p : ℕ), p > 0 ∧ (f^[p]) ((f^[m]) x) = (f^[m]) x := by
  obtain ⟨i, k, hk_pos, hk⟩ := finite_orbit_implies_periodic f x h_fin
  use i, k
  constructor
  · exact hk_pos
  ·
    calc (f^[k]) ((f^[i]) x) = (f^[k + i]) x := by rw [Function.iterate_add_apply]
      _ = (f^[i + k]) x := by congr 1; omega
      _ = (f^[i]) x := hk

theorem no_orbit_point_periodic_implies_infinite (f : ℝ → ℝ) (x : ℝ)
    (h_no_periodic : ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f) :
    (orbitSet f x).Infinite := by
  by_contra h_fin
  simp only [Set.not_infinite] at h_fin
  obtain ⟨m, p, hp_pos, hp_eq⟩ := finite_orbit_has_periodic_point f x h_fin
  have h_in_orbit : (f^[m]) x ∈ orbitSet f x := orbitSet_iterate f x m
  have h_periodic : (f^[m]) x ∈ Function.periodicPts f :=
    Function.mk_mem_periodicPts hp_pos hp_eq
  exact h_no_periodic _ h_in_orbit h_periodic

theorem iterate_collision_implies_periodic (f : ℝ → ℝ) (x : ℝ) {m n : ℕ}
    (hmn : m < n) (heq : (f^[m]) x = (f^[n]) x) :
    (f^[m]) x ∈ Function.periodicPts f := by
  have hk_pos : 0 < n - m := Nat.sub_pos_of_lt hmn
  have h_period : (f^[n - m]) ((f^[m]) x) = (f^[m]) x := by
    calc (f^[n - m]) ((f^[m]) x) = (f^[n - m + m]) x := by rw [Function.iterate_add_apply]
      _ = (f^[n]) x := by congr 1; omega
      _ = (f^[m]) x := heq.symm
  exact Function.mk_mem_periodicPts hk_pos h_period

theorem iterate_injective_of_no_periodic_orbit (f : ℝ → ℝ) (x : ℝ)
    (h_no_periodic : ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f) :
    Function.Injective (fun n : ℕ => (f^[n]) x) := by
  intro m n heq
  by_contra hmn_ne
  wlog hmn : m < n generalizing m n
  · have hnm : n < m := Nat.lt_of_le_of_ne (Nat.not_lt.mp hmn) (Ne.symm hmn_ne)
    exact this heq.symm (Ne.symm hmn_ne) hnm

  have h_fm_periodic : (f^[m]) x ∈ Function.periodicPts f :=
    iterate_collision_implies_periodic f x hmn heq

  have h_fm_in_orbit : (f^[m]) x ∈ orbitSet f x := orbitSet_iterate f x m

  exact h_no_periodic _ h_fm_in_orbit h_fm_periodic

theorem no_periodic_orbit_of_orbitSet_infinite (f : ℝ → ℝ) (x : ℝ)
    (h_inf : (orbitSet f x).Infinite) :
    ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f := by
  intro y hy hy_per

  obtain ⟨m, hm⟩ := hy

  have hmp_pos : 0 < Function.minimalPeriod f y :=
    Function.minimalPeriod_pos_of_mem_periodicPts hy_per

  have h_orbit_x_finite : (orbitSet f x).Finite := by
    have h_pre : ({z | ∃ k, k < m ∧ (f^[k]) x = z} : Set ℝ).Finite := by
      have : {z | ∃ k, k < m ∧ (f^[k]) x = z} =
             (fun k => (f^[k]) x) '' (Finset.range m : Set ℕ) := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
      rw [this]
      exact Set.Finite.image _ (Finset.finite_toSet _)
    have h_post : ({z | ∃ k, k ≥ m ∧ (f^[k]) x = z} : Set ℝ).Finite := by
      have h_eq : {z | ∃ k, k ≥ m ∧ (f^[k]) x = z} = orbitSet f y := by
        ext z
        simp only [Set.mem_setOf_eq, orbitSet]
        constructor
        · rintro ⟨k, hk, rfl⟩
          use k - m
          calc (f^[k - m]) y = (f^[k - m]) ((f^[m]) x) := by rw [hm]
            _ = (f^[k - m + m]) x := by rw [Function.iterate_add_apply]
            _ = (f^[k]) x := by congr 1; omega
        · rintro ⟨j, rfl⟩
          use j + m
          constructor
          · omega
          · calc (f^[j + m]) x = (f^[j]) ((f^[m]) x) := by rw [Function.iterate_add_apply]
              _ = (f^[j]) y := by rw [hm]
      rw [h_eq]
      have h_orbit_y_subset : orbitSet f y ⊆
          {z | ∃ k < Function.minimalPeriod f y, (f^[k]) y = z} := by
        intro z hz
        obtain ⟨n, hn⟩ := hz
        use n % Function.minimalPeriod f y
        constructor
        · exact Nat.mod_lt n hmp_pos
        · rw [← hn]; exact Function.iterate_mod_minimalPeriod_eq
      have h_orbit_y_bound_finite :
          {z | ∃ k < Function.minimalPeriod f y, (f^[k]) y = z}.Finite := by
        have : {z | ∃ k < Function.minimalPeriod f y, (f^[k]) y = z} =
               (fun k => (f^[k]) y) '' (Finset.range (Function.minimalPeriod f y) : Set ℕ) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
        rw [this]
        exact Set.Finite.image _ (Finset.finite_toSet _)
      exact h_orbit_y_bound_finite.subset h_orbit_y_subset
    have h_union : orbitSet f x = {z | ∃ k, k < m ∧ (f^[k]) x = z} ∪
                                  {z | ∃ k, k ≥ m ∧ (f^[k]) x = z} := by
      ext z
      simp only [Set.mem_union, Set.mem_setOf_eq, orbitSet]
      constructor
      · rintro ⟨k, rfl⟩
        by_cases hk : k < m
        · left; exact ⟨k, hk, rfl⟩
        · right; exact ⟨k, Nat.not_lt.mp hk, rfl⟩
      · rintro (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩)
        · exact ⟨k, rfl⟩
        · exact ⟨k, rfl⟩
    rw [h_union]
    exact Set.Finite.union h_pre h_post
  exact h_inf h_orbit_x_finite

theorem hasInfiniteOrbit_iff_orbitSet_infinite (f : ℝ → ℝ) (x : ℝ) :
    HasInfiniteOrbit f x ↔ (orbitSet f x).Infinite := by
  unfold HasInfiniteOrbit
  constructor
  · exact no_orbit_point_periodic_implies_infinite f x
  · exact no_periodic_orbit_of_orbitSet_infinite f x

end RealDynamics

namespace TDCSG.CompoundSymmetry.GG5

open Real Function Set RealDynamics
open TDCSG.Definitions

export TDCSG.Definitions (GG5_displacement cumulative_displacement)

end TDCSG.CompoundSymmetry.GG5
