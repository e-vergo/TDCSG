/-
Copyright (c) 2025 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.IET
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Orbit Theory for Real Functions

This file provides generic definitions and lemmas about orbits of real-valued functions.
These results are not specific to interval exchange transformations or GG5.

## Main definitions

* `orbitSet`: The orbit set of a point x under iteration of f
* `HasInfiniteOrbit`: A point has infinite orbit if it is not periodic (not in `periodicPts`)

## Main results

* `finite_orbit_has_collision`: Finite orbits have colliding iterates
* `finite_orbit_implies_periodic`: Finite orbits imply eventual periodicity
* `finite_orbit_has_periodic_point`: Finite orbits contain a periodic point
* `no_orbit_point_periodic_implies_infinite`: If no orbit point is periodic, orbit is infinite
* `hasInfiniteOrbit_iff_orbitSet_infinite`: Equivalence between not being periodic and having
  an infinite orbit set
-/

namespace Orbit

open Function Set

/-- The orbit set of a point x under iteration of f. -/
def orbitSet (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ (n : ℕ), (f^[n]) x = y}

/-- A point has infinite orbit if no point in its orbit is periodic.
    This is equivalent to the orbit set being infinite. -/
def HasInfiniteOrbit (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f

/-- The orbit of x contains x itself. -/
theorem mem_orbitSet_self (f : ℝ → ℝ) (x : ℝ) : x ∈ orbitSet f x := by
  use 0
  simp

/-- If f^[n] x = y, then y is in the orbit of x. -/
theorem mem_orbitSet_of_iterate (f : ℝ → ℝ) (x y : ℝ) (n : ℕ) (h : (f^[n]) x = y) :
    y ∈ orbitSet f x :=
  ⟨n, h⟩

/-- Orbits are closed under forward iteration. -/
theorem orbitSet_iterate (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    (f^[n]) x ∈ orbitSet f x :=
  ⟨n, rfl⟩

/-- If the orbit set is finite, then there exist distinct indices with equal iterates. -/
theorem finite_orbit_has_collision (f : ℝ → ℝ) (x : ℝ) (h_fin : (orbitSet f x).Finite) :
    ∃ (i j : ℕ), i < j ∧ (f^[i]) x = (f^[j]) x := by
  -- Get a finset representation
  obtain ⟨s, hs⟩ := Set.Finite.exists_finset_coe h_fin
  let n := s.card
  -- Consider the first n+1 iterates: f^[0] x, f^[1] x, ..., f^[n] x
  -- All must be in s (which has n elements), so by pigeonhole, two must be equal
  have h_all_in_s : ∀ k ≤ n, (f^[k]) x ∈ s := by
    intro k _
    have : (f^[k]) x ∈ orbitSet f x := orbitSet_iterate f x k
    rw [← hs] at this
    exact this
  -- Use pigeonhole principle
  -- Among n+1 elements mapping into a set of size n, two must collide
  by_contra h_no_collision
  push_neg at h_no_collision
  -- All f^[k] x for k ≤ n are distinct
  have h_all_distinct : ∀ i j, i ≤ n → j ≤ n → i ≠ j → (f^[i]) x ≠ (f^[j]) x := by
    intro i j hi hj hij
    by_cases h : i < j
    · intro heq
      exact h_no_collision i j h heq
    · intro heq
      push_neg at h
      have hji : j < i := Nat.lt_of_le_of_ne h (Ne.symm hij)
      exact h_no_collision j i hji heq.symm
  -- The image {f^[k] x | k ≤ n} has size exactly n+1
  -- But this image is contained in s which has size n - contradiction
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

/-- If the orbit set is finite, the point is eventually periodic. -/
theorem finite_orbit_implies_periodic (f : ℝ → ℝ) (x : ℝ)
    (h_fin : (orbitSet f x).Finite) :
    ∃ (i k : ℕ), k > 0 ∧ (f^[i + k]) x = (f^[i]) x := by
  obtain ⟨i, j, hij, heq⟩ := finite_orbit_has_collision f x h_fin
  use i, j - i
  constructor
  · omega
  · calc (f^[i + (j - i)]) x = (f^[j]) x := by congr 1; omega
      _ = (f^[i]) x := heq.symm

/-- If x has a finite orbit, then either x itself is periodic,
    or some iterate of x is periodic. -/
theorem finite_orbit_has_periodic_point (f : ℝ → ℝ) (x : ℝ)
    (h_fin : (orbitSet f x).Finite) :
    ∃ (m p : ℕ), p > 0 ∧ (f^[p]) ((f^[m]) x) = (f^[m]) x := by
  obtain ⟨i, k, hk_pos, hk⟩ := finite_orbit_implies_periodic f x h_fin
  use i, k
  constructor
  · exact hk_pos
  · -- f^[i + k] x = f^[i] x means f^[k] (f^[i] x) = f^[i] x
    calc (f^[k]) ((f^[i]) x) = (f^[k + i]) x := by rw [Function.iterate_add_apply]
      _ = (f^[i + k]) x := by congr 1; omega
      _ = (f^[i]) x := hk

/-- If no point in the orbit of x is periodic, then the orbit is infinite. -/
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

/-- Helper: if f^[m] x = f^[n] x with m < n, then f^[m] x is periodic. -/
theorem iterate_collision_implies_periodic (f : ℝ → ℝ) (x : ℝ) {m n : ℕ}
    (hmn : m < n) (heq : (f^[m]) x = (f^[n]) x) :
    (f^[m]) x ∈ Function.periodicPts f := by
  have hk_pos : 0 < n - m := Nat.sub_pos_of_lt hmn
  have h_period : (f^[n - m]) ((f^[m]) x) = (f^[m]) x := by
    calc (f^[n - m]) ((f^[m]) x) = (f^[n - m + m]) x := by rw [Function.iterate_add_apply]
      _ = (f^[n]) x := by congr 1; omega
      _ = (f^[m]) x := heq.symm
  exact Function.mk_mem_periodicPts hk_pos h_period

/-- If no point in the orbit is periodic, all iterates are distinct. -/
theorem iterate_injective_of_no_periodic_orbit (f : ℝ → ℝ) (x : ℝ)
    (h_no_periodic : ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f) :
    Function.Injective (fun n : ℕ => (f^[n]) x) := by
  intro m n heq
  by_contra hmn_ne
  wlog hmn : m < n generalizing m n
  · have hnm : n < m := Nat.lt_of_le_of_ne (Nat.not_lt.mp hmn) (Ne.symm hmn_ne)
    exact this heq.symm (Ne.symm hmn_ne) hnm
  -- Now m < n and f^[m] x = f^[n] x
  -- This means f^[m] x is periodic
  have h_fm_periodic : (f^[m]) x ∈ Function.periodicPts f :=
    iterate_collision_implies_periodic f x hmn heq
  -- But f^[m] x is in the orbit
  have h_fm_in_orbit : (f^[m]) x ∈ orbitSet f x := orbitSet_iterate f x m
  -- This contradicts h_no_periodic
  exact h_no_periodic _ h_fm_in_orbit h_fm_periodic

/-- A point with infinite orbit set has no periodic points in its orbit. -/
theorem no_periodic_orbit_of_orbitSet_infinite (f : ℝ → ℝ) (x : ℝ)
    (h_inf : (orbitSet f x).Infinite) :
    ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f := by
  intro y hy hy_per
  -- y ∈ orbitSet f x means y = f^[m] x for some m
  obtain ⟨m, hm⟩ := hy
  -- y ∈ periodicPts f means minimalPeriod f y > 0
  have hmp_pos : 0 < Function.minimalPeriod f y :=
    Function.minimalPeriod_pos_of_mem_periodicPts hy_per
  -- The orbit of x equals orbit of y union {f^[0] x, ..., f^[m-1] x}
  -- Since y is periodic, orbit of y is finite, so orbit of x is finite
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

/-- The equivalence theorem: HasInfiniteOrbit (defined as no orbit point periodic)
    is equivalent to the orbit set being infinite. -/
theorem hasInfiniteOrbit_iff_orbitSet_infinite (f : ℝ → ℝ) (x : ℝ) :
    HasInfiniteOrbit f x ↔ (orbitSet f x).Infinite := by
  unfold HasInfiniteOrbit
  constructor
  · exact no_orbit_point_periodic_implies_infinite f x
  · exact no_periodic_orbit_of_orbitSet_infinite f x

end Orbit
