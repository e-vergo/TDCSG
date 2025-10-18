/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Finite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality

/-!
# Examples of Piecewise Isometries

This file provides concrete, proven examples of piecewise isometries and demonstrations
of what does NOT constitute a piecewise isometry.

## Main examples

### Proven piecewise isometries:
- Identity map
- Half-plane reflection
- Simple square billiard

### Proven non-isometries (counterexamples):
- Constant functions
- Doubling map (stretches distances)
- Baker's map (stretches horizontally, compresses vertically)

These examples demonstrate:
- How to construct piecewise isometries
- How to verify the isometry property
- Common mistakes (metric mismatches, stretching)
- Construction patterns for applications

-/

universe u

namespace PiecewiseIsometry.Examples

open Set MeasureTheory PiecewiseIsometry

section BasicExamples

/-- The identity map as a piecewise isometry with trivial partition. -/
example : PiecewiseIsometry ℝ :=
  PiecewiseIsometry.id

/-- The identity is globally continuous (no discontinuities). -/
example : (PiecewiseIsometry.id : PiecewiseIsometry ℝ).discontinuitySet = ∅ := by
  unfold discontinuitySet
  simp only [PiecewiseIsometry.id, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
  exact frontier_univ

/-- A constant function is NOT a piecewise isometry (fails isometry property). -/
example : ¬∃ (pi : PiecewiseIsometry ℝ), ∀ x : ℝ, pi x = 0 := by
  intro ⟨pi, h⟩
  -- Take any two points: 0 and 1
  have h01 : (0 : ℝ) ≠ 1 := by norm_num
  obtain ⟨s, hs, h0s⟩ := pi.exists_mem_partition (0 : ℝ)
  obtain ⟨t, ht, h1t⟩ := pi.exists_mem_partition (1 : ℝ)
  by_cases hst : s = t
  · -- Both in the same piece: contradiction from isometry property
    subst hst
    have : dist (pi 0) (pi 1) = dist (0 : ℝ) 1 := pi.isometry_on_pieces s hs 0 h0s 1 h1t
    rw [h 0, h 1] at this
    norm_num at this
  · -- They're in different pieces. Use pigeonhole: some piece has ≥2 points
    have : ∃ (a b : ℝ), a ≠ b ∧ ∃ u ∈ pi.partition, a ∈ u ∧ b ∈ u := by
      by_cases h_exists_two : ∃ u ∈ pi.partition, ∃ a ∈ u, ∃ b ∈ u, a ≠ b
      · obtain ⟨u, hu, a, hau, b, hbu, hab⟩ := h_exists_two
        use a, b, hab, u, hu, hau, hbu
      · -- All pieces are subsingletons
        push_neg at h_exists_two
        exfalso
        have h_each_countable : ∀ u ∈ pi.partition, u.Countable := by
          intro u hu
          exact Set.Subsingleton.countable (fun _ hx _ hy => h_exists_two u hu _ hx _ hy)
        have h_univ_countable : (Set.univ : Set ℝ).Countable := by
          rw [← pi.partition_cover]
          exact Set.Countable.sUnion pi.partition_countable h_each_countable
        exact Set.not_countable_univ h_univ_countable
    obtain ⟨a, b, hab, u, hu, hau, hbu⟩ := this
    have : dist (pi a) (pi b) = dist a b := pi.isometry_on_pieces u hu a hau b hbu
    rw [h a, h b] at this
    simp only [dist_self] at this
    exact hab (dist_eq_zero.mp this.symm)

end BasicExamples

section PlanarExamples

/-- A simple reflection: reflect left half across y-axis, keep right half fixed. -/
noncomputable def half_plane_reflection : PiecewiseIsometry (ℝ × ℝ) where
  partition := {
    {p : ℝ × ℝ | p.1 < 0},
    {p : ℝ × ℝ | p.1 ≥ 0}
  }
  partition_countable := by
    simp only [Set.countable_insert, Set.countable_singleton]
  partition_measurable := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · show MeasurableSet {p : ℝ × ℝ | p.1 < 0}
      have : {p : ℝ × ℝ | p.1 < 0} = Prod.fst ⁻¹' (Set.Iio (0 : ℝ)) := by
        ext p; simp [Set.Iio]
      rw [this]
      exact isOpen_Iio.measurableSet.preimage measurable_fst
    · show MeasurableSet {p : ℝ × ℝ | p.1 ≥ 0}
      have : {p : ℝ × ℝ | p.1 ≥ 0} = Prod.fst ⁻¹' (Set.Ici (0 : ℝ)) := by
        ext p; simp [Set.Ici]
      rw [this]
      exact isClosed_Ici.measurableSet.preimage measurable_fst
  partition_cover := by
    ext p
    simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : p.1 < 0
    · exact ⟨{p : ℝ × ℝ | p.1 < 0}, Or.inl rfl, h⟩
    · exact ⟨{p : ℝ × ℝ | p.1 ≥ 0}, Or.inr rfl, le_of_not_gt h⟩
  partition_nonempty := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · use (-1, 0); norm_num
    · use (1, 0); norm_num
  partition_disjoint := by
    intro s hs t ht hst
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with (rfl | rfl)
    · rcases ht with (rfl | rfl)
      · contradiction
      · apply Set.disjoint_left.mpr
        intro p (hp1 : p.1 < 0) (hp2 : p.1 ≥ 0)
        linarith [hp1, hp2]
    · rcases ht with (rfl | rfl)
      · apply Set.disjoint_left.mpr
        intro p (hp1 : p.1 ≥ 0) (hp2 : p.1 < 0)
        linarith [hp1, hp2]
      · contradiction
  toFun := fun p => if p.1 < 0 then (-p.1, p.2) else p
  isometry_on_pieces := by
    intro s hs x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · -- Piece: {p | p.1 < 0}, map: p ↦ (-p.1, p.2)
      simp only [Set.mem_setOf_eq] at hx hy
      have hx_if : (if x.1 < 0 then (-x.1, x.2) else x) = (-x.1, x.2) := by simp [hx]
      have hy_if : (if y.1 < 0 then (-y.1, y.2) else y) = (-y.1, y.2) := by simp [hy]
      rw [hx_if, hy_if]
      simp only [Prod.dist_eq, Real.dist_eq, neg_sub_neg, abs_sub_comm]
    · -- Piece: {p | p.1 ≥ 0}, map: p ↦ p (identity)
      simp only [Set.mem_setOf_eq] at hx hy
      have hx_if : (if x.1 < 0 then (-x.1, x.2) else x) = x := by simp [show ¬x.1 < 0 from not_lt.mpr hx]
      have hy_if : (if y.1 < 0 then (-y.1, y.2) else y) = y := by simp [show ¬y.1 < 0 from not_lt.mpr hy]
      rw [hx_if, hy_if]

end PlanarExamples

section SquareBilliard

/-- A simplified square billiard using identity map on both pieces. -/
noncomputable def square_billiard_simple : PiecewiseIsometry (ℝ × ℝ) where
  partition := {
    {p : ℝ × ℝ | p.1 < 1 ∧ p.2 < 1},
    {p : ℝ × ℝ | p.1 ≥ 1 ∨ p.2 ≥ 1}
  }
  partition_countable := by
    simp only [Set.countable_insert, Set.countable_singleton]
  partition_measurable := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · show MeasurableSet {p : ℝ × ℝ | p.1 < 1 ∧ p.2 < 1}
      have : {p : ℝ × ℝ | p.1 < 1 ∧ p.2 < 1} = Set.Iio (1 : ℝ) ×ˢ Set.Iio 1 := by
        ext p; simp [Set.Iio, Set.prod]
      rw [this]
      exact isOpen_Iio.prod isOpen_Iio |>.measurableSet
    · show MeasurableSet {p : ℝ × ℝ | p.1 ≥ 1 ∨ p.2 ≥ 1}
      have : {p : ℝ × ℝ | p.1 ≥ 1 ∨ p.2 ≥ 1} = (Set.Iio (1 : ℝ) ×ˢ Set.Iio 1)ᶜ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio]
        constructor
        · intro h
          intro ⟨h1, h2⟩
          cases h with
          | inl h => linarith
          | inr h => linarith
        · intro h
          by_cases h1 : p.1 < 1
          · have h2 : ¬p.2 < 1 := fun h2 => h ⟨h1, h2⟩
            exact Or.inr (le_of_not_lt h2)
          · exact Or.inl (le_of_not_lt h1)
      rw [this]
      exact (isOpen_Iio.prod isOpen_Iio |>.measurableSet).compl
  partition_cover := by
    ext p
    simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h1 : p.1 < 1 ∧ p.2 < 1
    · use {q : ℝ × ℝ | q.1 < 1 ∧ q.2 < 1}
      exact ⟨Or.inl rfl, h1⟩
    · use {q : ℝ × ℝ | q.1 ≥ 1 ∨ q.2 ≥ 1}
      refine ⟨Or.inr rfl, ?_⟩
      simp only [not_and_or] at h1
      cases h1 with
      | inl h1 => exact Or.inl (le_of_not_lt h1)
      | inr h1 => exact Or.inr (le_of_not_lt h1)
  partition_disjoint := by
    intro s hs t ht hst
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
    · contradiction
    · apply Set.disjoint_left.mpr
      intro p ⟨h1, h2⟩ h3
      cases h3 with
      | inl h3 => linarith
      | inr h3 => linarith
    · apply Set.disjoint_left.mpr
      intro p h1 ⟨h2, h3⟩
      cases h1 with
      | inl h1 => linarith
      | inr h1 => linarith
    · contradiction
  toFun := id
  partition_nonempty := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · use (0.5, 0.5); norm_num
    · use (2, 2); norm_num
  isometry_on_pieces := by
    intro s hs x hx y hy
    rfl

/-- The discontinuity set is contained in the lines x=1 or y=1. -/
theorem square_billiard_boundary_discontinuity :
    square_billiard_simple.discontinuitySet ⊆
      {p : ℝ × ℝ | p.1 = 1 ∨ p.2 = 1} := by
  unfold discontinuitySet
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨s, hs, hp_front⟩ := hp
  have hs_cases : s = {p : ℝ × ℝ | p.1 < 1 ∧ p.2 < 1} ∨ s = {p : ℝ × ℝ | p.1 ≥ 1 ∨ p.2 ≥ 1} := by
    cases hs with
    | inl h => exact Or.inl h
    | inr h =>
      simp only [Set.mem_singleton_iff] at h
      exact Or.inr h
  cases hs_cases with
  | inl h_eq =>
    rw [h_eq] at hp_front
    have : {q : ℝ × ℝ | q.1 < 1 ∧ q.2 < 1} = Set.Iio (1 : ℝ) ×ˢ Set.Iio 1 := by
      ext; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iio]
    rw [this] at hp_front
    rw [frontier_prod_eq] at hp_front
    have h_front : frontier (Set.Iio (1 : ℝ)) = {1} := frontier_Iio
    have h_clos : closure (Set.Iio (1 : ℝ)) = Set.Iic 1 := closure_Iio' (by use 0; norm_num)
    rw [h_front, h_clos] at hp_front
    simp only [Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_singleton_iff] at hp_front
    cases hp_front with
    | inl h => exact Or.inr h.2
    | inr h => exact Or.inl h.1
  | inr h_eq =>
    rw [h_eq] at hp_front
    have h_compl : {q : ℝ × ℝ | q.1 ≥ 1 ∨ q.2 ≥ 1} = (Set.Iio (1 : ℝ) ×ˢ Set.Iio 1)ᶜ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio]
      constructor
      · intro h ⟨h1, h2⟩
        cases h with
        | inl h => linarith
        | inr h => linarith
      · intro h
        by_cases h1 : q.1 < 1
        · have : ¬q.2 < 1 := fun h2 => h ⟨h1, h2⟩
          exact Or.inr (le_of_not_lt this)
        · exact Or.inl (le_of_not_lt h1)
    rw [h_compl] at hp_front
    rw [frontier_compl] at hp_front
    rw [frontier_prod_eq] at hp_front
    have h_front : frontier (Set.Iio (1 : ℝ)) = {1} := frontier_Iio
    have h_clos : closure (Set.Iio (1 : ℝ)) = Set.Iic 1 := closure_Iio' (by use 0; norm_num)
    rw [h_front, h_clos] at hp_front
    simp only [Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_singleton_iff] at hp_front
    cases hp_front with
    | inl h => exact Or.inr h.2
    | inr h => exact Or.inl h.1

end SquareBilliard

section ChaoticExamples

/-- The doubling map x ↦ 2x mod 1 on [0,1).
    This is NOT an isometry! It stretches distances by factor 2. -/
noncomputable def doubling_map_NON_ISOMETRY : ℝ → ℝ := fun x =>
  if 0 ≤ x ∧ x < 1 then 2 * x - ⌊2 * x⌋ else x

/-- The doubling map is NOT a piecewise isometry (fails distance preservation). -/
example : ¬∃ (pi : PiecewiseIsometry ℝ), ∀ x ∈ Ico (0 : ℝ) 1, pi x = doubling_map_NON_ISOMETRY x := by
  intro ⟨pi, h⟩
  have : ∃ u ∈ pi.partition, ∃ a b, a ≠ b ∧ a ∈ Icc 0.1 0.2 ∧ b ∈ Icc 0.1 0.2 ∧ a ∈ u ∧ b ∈ u := by
    by_contra h_contra
    push_neg at h_contra
    have : Set.Countable (Icc (0.1 : ℝ) 0.2) := by
      have each_sub : ∀ s ∈ pi.partition, Set.Subsingleton (s ∩ Icc (0.1 : ℝ) 0.2) := by
        intro s hs a ⟨has, ha⟩ b ⟨hbs, hb⟩
        by_contra hab
        exact h_contra s hs a b hab ha hb has hbs
      have each_countable : ∀ s ∈ pi.partition, (s ∩ Icc (0.1 : ℝ) 0.2).Countable := by
        intro s hs
        exact Set.Subsingleton.countable (each_sub s hs)
      have eq_biUnion : Icc (0.1 : ℝ) 0.2 = ⋃ s ∈ pi.partition, s ∩ Icc (0.1 : ℝ) 0.2 := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hx
          obtain ⟨s, hs, hxs⟩ := pi.exists_mem_partition x
          exact ⟨s, hs, hxs, hx⟩
        · intro ⟨s, hs, _, hx⟩
          exact hx
      rw [eq_biUnion]
      exact Set.Countable.biUnion pi.partition_countable each_countable
    have not_countable : ¬(Icc (0.1 : ℝ) 0.2).Countable := by
      intro h_count
      have h_le : Cardinal.mk (Icc (0.1 : ℝ) 0.2) ≤ Cardinal.aleph0 := by
        rwa [Cardinal.le_aleph0_iff_set_countable]
      have h_eq : Cardinal.mk (Icc (0.1 : ℝ) 0.2) = Cardinal.continuum :=
        Cardinal.mk_Icc_real (by norm_num : (0.1 : ℝ) < 0.2)
      rw [h_eq] at h_le
      exact Cardinal.aleph0_lt_continuum.not_ge h_le
    exact not_countable this
  obtain ⟨u, hu, a, b, hab, ha, hb, hau, hbu⟩ := this
  have ha_ico : a ∈ Ico (0 : ℝ) 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hb_ico : b ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have ha_double : doubling_map_NON_ISOMETRY a = 2 * a := by
    unfold doubling_map_NON_ISOMETRY
    have ha_cond : 0 ≤ a ∧ a < 1 := ha_ico
    rw [if_pos ha_cond]
    have h1 : 2 * a < 1 := by linarith [ha.2]
    have h2 : 0 ≤ 2 * a := by linarith [ha.1]
    have : ⌊2 * a⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h2, h1⟩
    simp [this]
  have hb_double : doubling_map_NON_ISOMETRY b = 2 * b := by
    unfold doubling_map_NON_ISOMETRY
    have hb_cond : 0 ≤ b ∧ b < 1 := hb_ico
    rw [if_pos hb_cond]
    have h1 : 2 * b < 1 := by linarith [hb.2]
    have h2 : 0 ≤ 2 * b := by linarith [hb.1]
    have : ⌊2 * b⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h2, h1⟩
    simp [this]
  have iso : dist (pi a) (pi b) = dist a b := pi.isometry_on_pieces u hu a hau b hbu
  rw [h a ha_ico, h b hb_ico, ha_double, hb_double] at iso
  have : dist (2 * a) (2 * b) = 2 * dist a b := by
    simp only [Real.dist_eq]
    rw [show 2 * a - 2 * b = 2 * (a - b) by ring]
    rw [abs_mul, abs_two, abs_sub_comm]
  rw [this] at iso
  exact hab (dist_eq_zero.mp (by linarith : dist a b = 0))

/-- The baker's map: another non-isometry example (stretches horizontally, compresses vertically). -/
noncomputable def baker_map_NON_ISOMETRY : ℝ × ℝ → ℝ × ℝ := fun p =>
  if p.1 < 1/2 then (2 * p.1, p.2 / 2)
  else (2 * p.1 - 1, (p.2 + 1) / 2)

/-- The baker's map is NOT a piecewise isometry. -/
example : ¬∃ (pi : PiecewiseIsometry (ℝ × ℝ)),
    ∀ p, p.1^2 + p.2^2 < 1 → pi p = baker_map_NON_ISOMETRY p := by
  intro ⟨pi, h⟩
  let a : ℝ × ℝ := (0.1, 0)
  let b : ℝ × ℝ := (0.2, 0)
  have ha_disk : a.1^2 + a.2^2 < 1 := by norm_num
  have hb_disk : b.1^2 + b.2^2 < 1 := by norm_num
  have hab : a ≠ b := by
    intro h_eq
    have : (0.1 : ℝ) = 0.2 := by simpa using (Prod.ext_iff.mp h_eq).1
    norm_num at this
  obtain ⟨u, hu, hau⟩ := pi.exists_mem_partition a
  obtain ⟨v, hv, hbv⟩ := pi.exists_mem_partition b
  by_cases same_piece : u = v
  · subst same_piece
    have iso : dist (pi a) (pi b) = dist a b := pi.isometry_on_pieces u hu a hau b hbv
    have ha_baker : baker_map_NON_ISOMETRY a = (0.2, 0) := by
      unfold baker_map_NON_ISOMETRY; simp; norm_num
    have hb_baker : baker_map_NON_ISOMETRY b = (0.4, 0) := by
      unfold baker_map_NON_ISOMETRY; simp; norm_num
    rw [h a ha_disk, h b hb_disk, ha_baker, hb_baker] at iso
    have dist_ab : dist a b = 0.1 := by
      rw [dist_prod_same_right]; simp [Real.dist_eq]; norm_num
    have dist_images : dist ((0.2, 0) : ℝ × ℝ) (0.4, 0) = 0.2 := by
      rw [dist_prod_same_right]; simp [Real.dist_eq]; norm_num
    rw [dist_ab, dist_images] at iso
    norm_num at iso
  · have : ∃ u ∈ pi.partition, ∃ p q : ℝ × ℝ, p ≠ q ∧
        p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0 ∧ q.1 ∈ Icc 0.1 0.2 ∧ q.2 = 0 ∧ p ∈ u ∧ q ∈ u := by
      by_contra h_contra
      push_neg at h_contra
      have : Set.Countable {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0} := by
        have each_sub : ∀ s ∈ pi.partition,
            Set.Subsingleton (s ∩ {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0}) := by
          intro s hs p ⟨hps, hp1, hp2⟩ q ⟨hqs, hq1, hq2⟩
          by_contra hpq
          exact h_contra s hs p q hpq hp1 hp2 hq1 hq2 hps hqs
        have each_countable : ∀ s ∈ pi.partition,
            (s ∩ {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0}).Countable := by
          intro s hs
          exact Set.Subsingleton.countable (each_sub s hs)
        have eq_biUnion : {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0} =
            ⋃ s ∈ pi.partition, s ∩ {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0} := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
          constructor
          · intro ⟨hp1, hp2⟩
            obtain ⟨s, hs, hps⟩ := pi.exists_mem_partition p
            exact ⟨s, hs, hps, hp1, hp2⟩
          · intro ⟨s, hs, _, hp1, hp2⟩
            exact ⟨hp1, hp2⟩
        rw [eq_biUnion]
        exact Set.Countable.biUnion pi.partition_countable each_countable
      have not_countable : ¬Set.Countable {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0} := by
        intro h_count
        have : Set.Countable (Icc (0.1 : ℝ) 0.2) := by
          have inj : Function.Injective (fun x : Icc (0.1 : ℝ) 0.2 => (x.val, (0 : ℝ))) := by
            intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
            have : x = y := by
              have : (x, (0 : ℝ)) = (y, 0) := h_eq
              exact (Prod.ext_iff.mp this).1
            exact Subtype.ext this
          let f : {p : ℝ × ℝ | p.1 ∈ Icc 0.1 0.2 ∧ p.2 = 0} → Icc (0.1 : ℝ) 0.2 :=
            fun ⟨p, hp⟩ => ⟨p.1, hp.1⟩
          have f_inj : Function.Injective f := by
            intro ⟨⟨x1, y1⟩, hx1, hy1⟩ ⟨⟨x2, y2⟩, hx2, hy2⟩ h_eq
            simp [f] at h_eq
            ext
            · exact h_eq
            · rw [hy1, hy2]
          have : Countable (Icc (0.1 : ℝ) 0.2) := by
            have h_count_subtype := h_count.to_subtype
            have f_surj : Function.Surjective f := by
              intro ⟨x, hx⟩
              use ⟨(x, 0), hx, rfl⟩
            exact Function.Surjective.countable f_surj
          exact Set.countable_coe_iff.mp this
        have h_le : Cardinal.mk (Icc (0.1 : ℝ) 0.2) ≤ Cardinal.aleph0 := by
          rwa [Cardinal.le_aleph0_iff_set_countable]
        have h_eq : Cardinal.mk (Icc (0.1 : ℝ) 0.2) = Cardinal.continuum :=
          Cardinal.mk_Icc_real (by norm_num : (0.1 : ℝ) < 0.2)
        rw [h_eq] at h_le
        exact Cardinal.aleph0_lt_continuum.not_ge h_le
      exact not_countable this
    obtain ⟨u, hu, p, q, hpq, hp1, hp2, hq1, hq2, hpu, hqu⟩ := this
    have hp_disk : p.1^2 + p.2^2 < 1 := by
      rw [hp2]; simp; exact abs_lt.mpr ⟨by linarith [hp1.1], by linarith [hp1.2]⟩
    have hq_disk : q.1^2 + q.2^2 < 1 := by
      rw [hq2]; simp; exact abs_lt.mpr ⟨by linarith [hq1.1], by linarith [hq1.2]⟩
    have iso : dist (pi p) (pi q) = dist p q := pi.isometry_on_pieces u hu p hpu q hqu
    have hp_left : p.1 < 1/2 := by linarith [hp1.2]
    have hq_left : q.1 < 1/2 := by linarith [hq1.2]
    have hp_baker : baker_map_NON_ISOMETRY p = (2 * p.1, p.2 / 2) := by
      unfold baker_map_NON_ISOMETRY
      rw [if_pos hp_left]
    have hq_baker : baker_map_NON_ISOMETRY q = (2 * q.1, q.2 / 2) := by
      unfold baker_map_NON_ISOMETRY
      rw [if_pos hq_left]
    rw [h p hp_disk, h q hq_disk, hp_baker, hq_baker] at iso
    have dist_pq : dist p q = dist p.1 q.1 := by
      have hp_form : p = (p.1, 0) := Prod.ext rfl hp2
      have hq_form : q = (q.1, 0) := Prod.ext rfl hq2
      rw [hp_form, hq_form]
      exact dist_prod_same_right
    have dist_images : dist (2 * p.1, p.2 / 2) (2 * q.1, q.2 / 2) = dist (2 * p.1) (2 * q.1) := by
      have hp2_div : p.2 / 2 = 0 := by rw [hp2]; norm_num
      have hq2_div : q.2 / 2 = 0 := by rw [hq2]; norm_num
      rw [hp2_div, hq2_div]
      exact dist_prod_same_right
    rw [dist_images] at iso
    have double_dist : dist (2 * p.1) (2 * q.1) = 2 * dist p.1 q.1 := by
      simp only [Real.dist_eq]
      rw [show 2 * p.1 - 2 * q.1 = 2 * (p.1 - q.1) by ring]
      rw [abs_mul, abs_two, abs_sub_comm]
    rw [double_dist, dist_pq] at iso
    have : dist p.1 q.1 = 0 := by linarith
    have : p.1 = q.1 := dist_eq_zero.mp this
    have : p = q := by
      ext
      · exact ‹p.1 = q.1›
      · rw [hp2, hq2]
    exact hpq this

end ChaoticExamples

section ConstructionPatterns

/-- Pattern: construct a piecewise isometry from explicit pieces and maps. -/
example : PiecewiseIsometry ℝ := by
  exact PiecewiseIsometry.id

/-- Pattern: construct from a list of pieces for finite partitions. -/
example : FinitePiecewiseIsometry ℝ := {
  partition := {Set.Iio (0 : ℝ), Set.Ici 0}
  partition_finite := by
    simp only [Set.finite_singleton, Set.Finite.insert]
  partition_countable := by
    exact Set.Finite.countable (by simp only [Set.finite_singleton, Set.Finite.insert])
  partition_measurable := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · exact isOpen_Iio.measurableSet
    · exact isClosed_Ici.measurableSet
  partition_cover := by
    ext x
    simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_univ, iff_true]
    by_cases h : x < 0
    · exact ⟨Set.Iio 0, Or.inl rfl, h⟩
    · exact ⟨Set.Ici 0, Or.inr rfl, le_of_not_gt h⟩
  partition_nonempty := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · use (-1 : ℝ); norm_num
    · use (0 : ℝ); norm_num
  partition_disjoint := by
    intro s hs t ht hst
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
    · contradiction
    · apply Set.disjoint_left.mpr
      intro x (hx : x < 0) (hx' : 0 ≤ x)
      linarith
    · apply Set.disjoint_left.mpr
      intro x (hx : 0 ≤ x) (hx' : x < 0)
      linarith
    · contradiction
  toFun := id
  isometry_on_pieces := by
    intro s hs x hx y hy
    rfl
}

end ConstructionPatterns

end PiecewiseIsometry.Examples
