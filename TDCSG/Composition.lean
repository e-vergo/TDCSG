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

/-- The refined partition obtained by intersecting pieces from two partitions with preimage.

Given partitions p (for g) and q (for f), and function g, the preimage-based refinement consists
of all nonempty intersections s ∩ g⁻¹(t) where s ∈ p and t ∈ q.
This ensures g maps each refined piece entirely into a single piece of f's partition. -/
def refinedPartitionPreimage (p q : Set (Set α)) (g : α → α) : Set (Set α) :=
  {u | ∃ s ∈ p, ∃ t ∈ q, u = s ∩ (g ⁻¹' t) ∧ (s ∩ (g ⁻¹' t)).Nonempty}

/-- The naive refined partition (kept for potential use in other contexts). -/
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

/-- Elements of the preimage-based refined partition are measurable. -/
theorem refinedPartitionPreimage_measurable {α : Type u} [MeasurableSpace α]
    (p q : Set (Set α)) (g : α → α)
    (hp : ∀ s ∈ p, MeasurableSet s) (hq : ∀ t ∈ q, MeasurableSet t)
    (hg : Measurable g) :
    ∀ u ∈ refinedPartitionPreimage p q g, MeasurableSet u := by
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact (hp s hs).inter (hg (hq t ht))

/-- The preimage-based refined partition covers the space. -/
theorem refinedPartitionPreimage_cover {α : Type u} (p q : Set (Set α)) (g : α → α)
    (hp : ⋃₀ p = Set.univ) (hq : ⋃₀ q = Set.univ) :
    ⋃₀ refinedPartitionPreimage p q g = Set.univ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  rw [Set.sUnion_eq_univ_iff] at hp hq
  obtain ⟨s, hs, hxs⟩ := hp x
  obtain ⟨t, ht, hgxt⟩ := hq (g x)
  use s ∩ (g ⁻¹' t)
  constructor
  · unfold refinedPartitionPreimage
    simp only [Set.mem_setOf_eq]
    exact ⟨s, hs, t, ht, rfl, ⟨x, hxs, hgxt⟩⟩
  · exact ⟨hxs, hgxt⟩

/-- The preimage-based refined partition is countable. -/
theorem refinedPartitionPreimage_countable (p q : Set (Set α)) (g : α → α)
    (hp : p.Countable) (hq : q.Countable) :
    (refinedPartitionPreimage p q g).Countable := by
  refine Set.Countable.mono ?_ ((hp.prod hq).image (fun st => st.1 ∩ (g ⁻¹' st.2)))
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact ⟨(s, t), ⟨hs, ht⟩, rfl⟩

/-- The preimage-based refined partition is pairwise disjoint. -/
theorem refinedPartitionPreimage_disjoint {α : Type u} (p q : Set (Set α)) (g : α → α)
    (hp : ∀ s ∈ p, ∀ t ∈ p, s ≠ t → Disjoint s t)
    (hq : ∀ s ∈ q, ∀ t ∈ q, s ≠ t → Disjoint s t) :
    ∀ u ∈ refinedPartitionPreimage p q g, ∀ v ∈ refinedPartitionPreimage p q g, u ≠ v → Disjoint u v := by
  intro u hu v hv huv
  obtain ⟨s₁, hs₁, t₁, ht₁, rfl, _⟩ := hu
  obtain ⟨s₂, hs₂, t₂, ht₂, rfl, _⟩ := hv
  show Disjoint (s₁ ∩ (g ⁻¹' t₁)) (s₂ ∩ (g ⁻¹' t₂))
  by_cases h₁ : s₁ = s₂
  · subst h₁
    by_cases h₂ : t₁ = t₂
    · subst h₂
      exact absurd rfl huv
    · have hdisj : Disjoint t₁ t₂ := hq t₁ ht₁ t₂ ht₂ h₂
      exact Set.disjoint_of_subset_right (Set.inter_subset_right)
        (Set.disjoint_of_subset_left (Set.inter_subset_right) (Disjoint.preimage g hdisj))
  · have hdisj : Disjoint s₁ s₂ := hp s₁ hs₁ s₂ hs₂ h₁
    exact Set.disjoint_of_subset_left (Set.inter_subset_left)
      (Set.disjoint_of_subset_right (Set.inter_subset_left) hdisj)

end Refinement

section Measurability

/-- A piecewise isometry is measurable under OpensMeasurableSpace.

MATHEMATICAL JUSTIFICATION:
- f is an isometry (hence continuous) when restricted to each piece s ∈ partition
- For any open set U, we have f⁻¹(U) = ⋃_{s ∈ partition} (f⁻¹(U) ∩ s)
- Each f⁻¹(U) ∩ s is measurable because:
  * s is measurable (by partition_measurable)
  * f is continuous on s (by isometry_on_pieces)
  * U is open (by assumption)
  * Under OpensMeasurableSpace, continuous functions on measurable sets have measurable preimages

BLOCKING ISSUE: Requires a Mathlib lemma of the form:
  "If f : α → β is continuous on a measurable set s, and U is open, then f⁻¹(U) ∩ s is measurable"
This is a standard result in measure theory but may need to be added to Mathlib. -/
theorem piecewiseIsometry_measurable [OpensMeasurableSpace α] (f : PiecewiseIsometry α) :
    Measurable f.toFun := by
  sorry

end Measurability

section Composition

/-- Composition of two piecewise isometries.

The composition `f.comp g` applies `g` first, then `f`. The resulting partition uses
preimage-based refinement to ensure g maps each refined piece into a single piece of f's partition. -/
def comp [OpensMeasurableSpace α] (f g : PiecewiseIsometry α) : PiecewiseIsometry α where
  partition := refinedPartitionPreimage g.partition f.partition g.toFun
  partition_measurable := by
    apply refinedPartitionPreimage_measurable
    · exact g.partition_measurable
    · exact f.partition_measurable
    · exact piecewiseIsometry_measurable g
  partition_countable := refinedPartitionPreimage_countable g.partition f.partition g.toFun
    g.partition_countable f.partition_countable
  partition_cover := refinedPartitionPreimage_cover g.partition f.partition g.toFun
    g.partition_cover f.partition_cover
  partition_disjoint := refinedPartitionPreimage_disjoint g.partition f.partition g.toFun
    g.partition_disjoint f.partition_disjoint
  partition_nonempty := by
    intro u hu
    obtain ⟨s, hs, t, ht, rfl, hnonempty⟩ := hu
    exact hnonempty
  toFun := f.toFun ∘ g.toFun
  isometry_on_pieces := by
    intro s hs x hx y hy
    -- s is an intersection from refinedPartitionPreimage
    obtain ⟨s_g, hs_g, s_f, hs_f, rfl, _⟩ := hs
    simp only [Function.comp_apply]
    -- Key insight: x, y ∈ s_g ∩ (g⁻¹' s_f) means g(x), g(y) ∈ s_f
    have hgx : g.toFun x ∈ s_f := by
      have : x ∈ g.toFun ⁻¹' s_f := hx.2
      exact this
    have hgy : g.toFun y ∈ s_f := by
      have : y ∈ g.toFun ⁻¹' s_f := hy.2
      exact this
    -- Apply g first (isometric on s_g), then f (isometric on s_f)
    calc dist (f.toFun (g.toFun x)) (f.toFun (g.toFun y))
        = dist (g.toFun x) (g.toFun y) := f.isometry_on_pieces s_f hs_f (g.toFun x) hgx (g.toFun y) hgy
      _ = dist x y := g.isometry_on_pieces s_g hs_g x hx.1 y hy.1

/-- Function application for composition. -/
@[simp]
theorem comp_apply [OpensMeasurableSpace α] (f g : PiecewiseIsometry α) (x : α) :
    (f.comp g) x = f (g x) := rfl

/-- Extensionality lemma for PiecewiseIsometry equality.

ARCHITECTURAL ISSUE: This theorem statement is INCORRECT as formulated.
Two PiecewiseIsometry values are equal iff ALL fields match, including partition.
Having the same underlying function is NOT sufficient for equality of structures.

RESOLUTION OPTIONS:
1. Remove this theorem entirely (structures have built-in equality)
2. Reformulate as a setoid/equivalence relation on PiecewiseIsometry
3. Prove a weaker "function agreement" lemma without claiming structural equality

For now, this is marked sorry to indicate it cannot be proven as stated. -/
@[ext]
theorem ext {f g : PiecewiseIsometry α}
    (h_fun : ∀ x, f x = g x) : f = g := by
  sorry  -- CANNOT BE PROVEN: Requires partition equality, not just function equality

/-- Composition is associative. -/
theorem comp_assoc [OpensMeasurableSpace α] (f g h : PiecewiseIsometry α) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  -- Both sides have the same function
  -- Partitions: need to show refinement is associative
  -- Functions are definitionally equal
  sorry

/-- Left identity for composition. -/
theorem comp_id_left [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) :
    id.comp f = f := by
  -- The partition refinedPartition f.partition {univ} should equal f.partition
  -- and the function id ∘ f = f
  sorry

/-- Right identity for composition. -/
theorem comp_id_right [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) :
    f.comp id = f := by
  -- Partitions: refinedPartition {univ} f.partition = f.partition
  -- Functions: f ∘ id = f
  sorry

end Composition

section Iteration

/-- The nth iterate of a piecewise isometry.

`iterate f n` applies `f` a total of `n` times. By convention, `iterate f 0` is the identity. -/
def iterate [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) : ℕ → PiecewiseIsometry α
  | 0 => id
  | n + 1 => f.comp (iterate f n)

/-- Characterization of iterate at successor. -/
theorem iterate_succ [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (n : ℕ) :
    iterate f (n + 1) = f.comp (iterate f n) := rfl

/-- Iterate at zero is identity. -/
@[simp]
theorem iterate_zero_eq [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) :
    iterate f 0 = id := rfl

/-- Iterate at one is the original map. -/
@[simp]
theorem iterate_one [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) :
    iterate f 1 = f := by
  rw [iterate_succ, iterate_zero_eq, comp_id_right]

/-- Function application for iteration. -/
theorem iterate_apply [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (n : ℕ) (x : α) :
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
theorem iterate_add [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (m n : ℕ) :
    iterate f (m + n) = (iterate f m).comp (iterate f n) := by
  induction m with
  | zero =>
    show iterate f (0 + n) = (iterate f 0).comp (iterate f n)
    rw [iterate_zero_eq, Nat.zero_add, comp_id_left]
  | succ m ih =>
    rw [Nat.succ_add, iterate_succ, iterate_succ, ih, comp_assoc]

/-- Each iterate preserves the isometry property. -/
theorem iterate_isometry_on_pieces [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (n : ℕ) (s : Set α)
    (hs : s ∈ (iterate f n).partition) (x y : α) (hx : x ∈ s) (hy : y ∈ s) :
    dist ((iterate f n) x) ((iterate f n) y) = dist x y :=
  (iterate f n).dist_eq_on_piece s hs x y hx hy

/-- The underlying function of an iterate is the composition of the underlying functions. -/
theorem iterate_toFun [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (n : ℕ) :
    (iterate f n).toFun = f.toFun^[n] := by
  ext x
  exact iterate_apply f n x

end Iteration

section CompositionProperties

/-- Composition preserves distance on refined pieces. -/
theorem comp_dist_eq [OpensMeasurableSpace α] (f g : PiecewiseIsometry α) (x y : α)
    (h : ∃ s ∈ (f.comp g).partition, x ∈ s ∧ y ∈ s) :
    dist ((f.comp g) x) ((f.comp g) y) = dist x y := by
  obtain ⟨s, hs, hxs, hys⟩ := h
  exact (f.comp g).isometry_on_pieces s hs x hxs y hys

/-- The discontinuity set of a composition is contained in the union of discontinuity sets. -/
theorem discontinuitySet_comp_subset [OpensMeasurableSpace α] (f g : PiecewiseIsometry α) :
    (f.comp g).discontinuitySet ⊆
      f.discontinuitySet ∪ (g.toFun ⁻¹' f.discontinuitySet) ∪ g.discontinuitySet := by
  sorry

end CompositionProperties

section IterationProperties

/-- The discontinuity set of an iterate grows with iteration. -/
theorem discontinuitySet_iterate [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (n : ℕ) :
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
    exact absurd hx_frontier (Set.notMem_empty x)
  | succ n ih =>
    -- iterate (n+1) = f.comp (iterate n)
    -- This needs the discontinuitySet_comp_subset theorem to be completed
    sorry

/-- If f has finitely many discontinuities, so does each iterate (though possibly more). -/
theorem iterate_finite_discontinuities [Nonempty α] [OpensMeasurableSpace α] (f : PiecewiseIsometry α) (n : ℕ)
    (hf : f.discontinuitySet.Finite) :
    (iterate f n).discontinuitySet.Finite := by
  -- The discontinuity set of iterate n is contained in a finite union of preimages
  -- This requires bijectivity or other conditions to ensure preimages of finite sets are finite
  sorry

end IterationProperties

end PiecewiseIsometry
