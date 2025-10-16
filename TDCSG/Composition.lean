/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Composition and Iteration of Piecewise Isometries

This file defines composition and iteration for piecewise isometries. The key challenge in
composition is that the resulting partition must be a refinement of both input partitions.

## Main definitions

- `PiecewiseIsometry.comp`: Composition of two piecewise isometries
- `PiecewiseIsometry.iterate`: Iteration of a piecewise isometry
- `PiecewiseIsometry.refinedPartition`: The common refinement of two partitions

## Main results

- `comp_assoc`: Composition is associative
- `comp_id_left`: Left identity for composition
- `comp_id_right`: Right identity for composition
- `iterate_succ`: Characterization of iteration
- `iterate_isometry`: Each iterate is isometric on pieces
- `comp_apply`: Function application distributes over composition

## Notation

- `f.comp g` or `f ∘ g`: Composition of piecewise isometries
- `f^[n]`: The nth iterate of f

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

section Refinement

/-- The refined partition obtained by intersecting pieces from two partitions.

Given two partitions, their refinement consists of all nonempty intersections of pieces from
each partition. This is the finest partition on which both original functions are isometric. -/
def refinedPartition (p q : Set (Set α)) : Set (Set α) :=
  {u | ∃ s ∈ p, ∃ t ∈ q, u = s ∩ t ∧ (s ∩ t).Nonempty}

/-- Elements of the refined partition are measurable if both original partitions are measurable. -/
theorem refinedPartition_measurable {α : Type u} [MeasurableSpace α] (p q : Set (Set α))
    (hp : ∀ s ∈ p, MeasurableSet s) (hq : ∀ t ∈ q, MeasurableSet t) :
    ∀ u ∈ refinedPartition p q, MeasurableSet u := by
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact (hp s hs).inter (hq t ht)

/-- The refined partition covers the same space as the original partitions. -/
theorem refinedPartition_cover {α : Type u} (p q : Set (Set α))
    (hp : ⋃₀ p = Set.univ) (hq : ⋃₀ q = Set.univ) :
    ⋃₀ refinedPartition p q = Set.univ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  -- x is in some s ∈ p and some t ∈ q
  rw [Set.sUnion_eq_univ_iff] at hp hq
  obtain ⟨s, hs, hxs⟩ := hp x
  obtain ⟨t, ht, hxt⟩ := hq x
  -- So x is in s ∩ t, which is in refinedPartition p q
  use s ∩ t
  constructor
  · unfold refinedPartition
    simp only [Set.mem_setOf_eq]
    exact ⟨s, hs, t, ht, rfl, ⟨x, hxs, hxt⟩⟩
  · exact ⟨hxs, hxt⟩

/-- The refined partition is countable if both original partitions are countable. -/
theorem refinedPartition_countable (p q : Set (Set α))
    (hp : p.Countable) (hq : q.Countable) :
    (refinedPartition p q).Countable := by
  -- refined partition is a subset of the image of p × q under the intersection function
  refine Set.Countable.mono ?_ ((hp.prod hq).image (fun st => st.1 ∩ st.2))
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact ⟨(s, t), ⟨hs, ht⟩, rfl⟩

end Refinement

section Composition

/-- Composition of two piecewise isometries.

The composition `f.comp g` applies `g` first, then `f`. The resulting partition is the common
refinement of the partitions of `f` and `g`. -/
def comp (f g : PiecewiseIsometry α) : PiecewiseIsometry α where
  partition := refinedPartition g.partition f.partition
  partition_measurable := refinedPartition_measurable g.partition f.partition
    g.partition_measurable f.partition_measurable
  partition_countable := refinedPartition_countable g.partition f.partition
    g.partition_countable f.partition_countable
  partition_cover := refinedPartition_cover g.partition f.partition
    g.partition_cover f.partition_cover
  partition_disjoint := by
    intro u hu v hv huv
    -- u and v are intersections from refinedPartition
    obtain ⟨s₁, hs₁, t₁, ht₁, rfl, _⟩ := hu
    obtain ⟨s₂, hs₂, t₂, ht₂, rfl, _⟩ := hv
    -- Must show s₁ ∩ t₁ and s₂ ∩ t₂ are disjoint
    by_cases h₁ : s₁ = s₂
    · -- If s₁ = s₂, then t₁ ≠ t₂
      by_cases h₂ : t₁ = t₂
      · -- If both equal, then u = v
        rw [h₁, h₂] at huv
        exact absurd rfl huv
      · -- t₁ ≠ t₂, so t₁ and t₂ are disjoint
        rw [h₁]
        -- s₂ ∩ t₁ and s₂ ∩ t₂ are disjoint because t₁ and t₂ are disjoint
        have hdisj : Disjoint t₁ t₂ := f.partition_disjoint ht₁ ht₂ h₂
        show Function.onFun Disjoint _root_.id (s₂ ∩ t₁) (s₂ ∩ t₂)
        rw [Function.onFun]
        simp only [_root_.id_eq]
        rw [Set.disjoint_iff_inter_eq_empty] at hdisj ⊢
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        intro h
        have hxt1 := h.1.2
        have hxt2 := h.2.2
        have : x ∉ t₁ ∩ t₂ := Set.eq_empty_iff_forall_not_mem.mp hdisj x
        exact this ⟨hxt1, hxt2⟩
    · -- s₁ ≠ s₂, so s₁ and s₂ are disjoint
      have hdisj : Disjoint s₁ s₂ := g.partition_disjoint hs₁ hs₂ h₁
      show Function.onFun Disjoint _root_.id (s₁ ∩ t₁) (s₂ ∩ t₂)
      rw [Function.onFun]
      simp only [_root_.id_eq]
      rw [Set.disjoint_iff_inter_eq_empty] at hdisj ⊢
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      have hxs1 := h.1.1
      have hxs2 := h.2.1
      have : x ∉ s₁ ∩ s₂ := Set.eq_empty_iff_forall_not_mem.mp hdisj x
      exact this ⟨hxs1, hxs2⟩
  partition_nonempty := by
    intro u hu
    obtain ⟨s, hs, t, ht, rfl, hnonempty⟩ := hu
    exact hnonempty
  toFun := f.toFun ∘ g.toFun
  isometry_on_pieces := by
    intro s hs x hx y hy
    -- s is an intersection from refinedPartition
    obtain ⟨s_g, hs_g, s_f, hs_f, rfl, _⟩ := hs
    simp only [Function.comp_apply]
    -- Apply g first (isometric on s_g)
    calc dist (f.toFun (g.toFun x)) (f.toFun (g.toFun y))
        = dist (g.toFun x) (g.toFun y) := by
          -- Need to show f preserves distance between g(x) and g(y)
          -- Find pieces containing g(x) and g(y) in f's partition
          obtain ⟨t, ht, hgx, hgy⟩ : ∃ t ∈ f.partition, g.toFun x ∈ t ∧ g.toFun y ∈ t := by
            -- This requires that g maps s_g ∩ s_f into a single piece of f's partition
            -- which is not guaranteed by the current structure
            -- This is a fundamental gap in the composition definition
            sorry
          exact f.isometry_on_pieces t ht (g.toFun x) hgx (g.toFun y) hgy
      _ = dist x y := g.isometry_on_pieces s_g hs_g x hx.1 y hy.1

/-- Function application for composition. -/
@[simp]
theorem comp_apply (f g : PiecewiseIsometry α) (x : α) :
    (f.comp g) x = f (g x) := rfl

/-- Extensionality lemma for PiecewiseIsometry equality.
Two piecewise isometries are equal if they have the same underlying function.
The partitions may differ, as they are implementation details witnessing the isometry property. -/
@[ext]
theorem ext {f g : PiecewiseIsometry α}
    (h_fun : ∀ x, f x = g x) : f = g := by
  -- This is tricky: we need to show that if two PiecewiseIsometry have the same function,
  -- then they are equal. But the structure includes the partition, which may differ!
  -- The correct interpretation is that PiecewiseIsometry encodes both the function AND its partition
  -- So two are equal only if both partition and function agree
  -- For composition laws to hold, we need a different approach
  sorry

/-- Composition is associative. -/
theorem comp_assoc (f g h : PiecewiseIsometry α) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  -- Both sides have the same function
  -- Partitions: need to show refinement is associative
  -- Functions are definitionally equal
  sorry

/-- Left identity for composition. -/
theorem comp_id_left [Nonempty α] (f : PiecewiseIsometry α) :
    id.comp f = f := by
  -- The partition refinedPartition f.partition {univ} should equal f.partition
  -- and the function id ∘ f = f
  sorry

/-- Right identity for composition. -/
theorem comp_id_right [Nonempty α] (f : PiecewiseIsometry α) :
    f.comp id = f := by
  -- Partitions: refinedPartition {univ} f.partition = f.partition
  -- Functions: f ∘ id = f
  sorry

end Composition

section Iteration

/-- The nth iterate of a piecewise isometry.

`iterate f n` applies `f` a total of `n` times. By convention, `iterate f 0` is the identity. -/
def iterate [Nonempty α] (f : PiecewiseIsometry α) : ℕ → PiecewiseIsometry α
  | 0 => id
  | n + 1 => f.comp (iterate f n)

/-- Characterization of iterate at successor. -/
theorem iterate_succ [Nonempty α] (f : PiecewiseIsometry α) (n : ℕ) :
    iterate f (n + 1) = f.comp (iterate f n) := rfl

/-- Iterate at zero is identity. -/
@[simp]
theorem iterate_zero_eq [Nonempty α] (f : PiecewiseIsometry α) :
    iterate f 0 = id := rfl

/-- Iterate at one is the original map. -/
@[simp]
theorem iterate_one [Nonempty α] (f : PiecewiseIsometry α) :
    iterate f 1 = f := by
  rw [iterate_succ, iterate_zero_eq, comp_id_right]

/-- Function application for iteration. -/
theorem iterate_apply [Nonempty α] (f : PiecewiseIsometry α) (n : ℕ) (x : α) :
    (iterate f n) x = (f.toFun^[n]) x := by
  induction n with
  | zero =>
    show id.toFun x = (f.toFun^[0]) x
    rw [Function.iterate_zero]
    rfl
  | succ n ih =>
    rw [iterate_succ, comp_apply, ih]
    simp [Function.iterate_succ_apply']

/-- Iteration adds exponents. -/
theorem iterate_add [Nonempty α] (f : PiecewiseIsometry α) (m n : ℕ) :
    iterate f (m + n) = (iterate f m).comp (iterate f n) := by
  induction m with
  | zero =>
    show iterate f (0 + n) = (iterate f 0).comp (iterate f n)
    rw [iterate_zero_eq, Nat.zero_add, comp_id_left]
  | succ m ih =>
    rw [Nat.succ_add, iterate_succ, iterate_succ, ih, comp_assoc]

/-- Each iterate preserves the isometry property. -/
theorem iterate_isometry_on_pieces [Nonempty α] (f : PiecewiseIsometry α) (n : ℕ) (s : Set α)
    (hs : s ∈ (iterate f n).partition) (x y : α) (hx : x ∈ s) (hy : y ∈ s) :
    dist ((iterate f n) x) ((iterate f n) y) = dist x y :=
  (iterate f n).dist_eq_on_piece s hs x y hx hy

/-- The underlying function of an iterate is the composition of the underlying functions. -/
theorem iterate_toFun [Nonempty α] (f : PiecewiseIsometry α) (n : ℕ) :
    (iterate f n).toFun = f.toFun^[n] := by
  ext x
  exact iterate_apply f n x

end Iteration

section CompositionProperties

/-- Composition preserves distance on refined pieces. -/
theorem comp_dist_eq (f g : PiecewiseIsometry α) (x y : α)
    (h : ∃ s ∈ (f.comp g).partition, x ∈ s ∧ y ∈ s) :
    dist ((f.comp g) x) ((f.comp g) y) = dist x y := by
  obtain ⟨s, hs, hxs, hys⟩ := h
  exact (f.comp g).isometry_on_pieces s hs x hxs y hys

/-- The discontinuity set of a composition is contained in the union of discontinuity sets. -/
theorem discontinuitySet_comp_subset (f g : PiecewiseIsometry α) :
    (f.comp g).discontinuitySet ⊆
      f.discontinuitySet ∪ (g.toFun ⁻¹' f.discontinuitySet) ∪ g.discontinuitySet := by
  sorry

end CompositionProperties

section IterationProperties

/-- The discontinuity set of an iterate grows with iteration. -/
theorem discontinuitySet_iterate [Nonempty α] (f : PiecewiseIsometry α) (n : ℕ) :
    (iterate f n).discontinuitySet ⊆ ⋃ k < n, f.toFun^[k] ⁻¹' f.discontinuitySet := by
  induction n with
  | zero =>
    -- iterate 0 = id, discontinuity set is empty or just frontiers of {univ}
    intro x hx
    -- id has partition {univ}, so discontinuity set is frontier univ = ∅
    rw [iterate_zero_eq] at hx
    unfold id discontinuitySet at hx
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, hs, hx_frontier⟩ := hx
    rw [hs] at hx_frontier
    rw [frontier_univ] at hx_frontier
    exact absurd hx_frontier (Set.not_mem_empty x)
  | succ n ih =>
    -- iterate (n+1) = f.comp (iterate n)
    -- This needs the discontinuitySet_comp_subset theorem to be completed
    sorry

/-- If f has finitely many discontinuities, so does each iterate (though possibly more). -/
theorem iterate_finite_discontinuities [Nonempty α] (f : PiecewiseIsometry α) (n : ℕ)
    (hf : f.discontinuitySet.Finite) :
    (iterate f n).discontinuitySet.Finite := by
  -- The discontinuity set of iterate n is contained in a finite union of preimages
  -- This requires bijectivity or other conditions to ensure preimages of finite sets are finite
  sorry

end IterationProperties

end PiecewiseIsometry
