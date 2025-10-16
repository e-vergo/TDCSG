/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Properties of Piecewise Isometries

This file develops basic properties and lemmas for working with piecewise isometries, including:
- Properties of partitions and their measurability
- Relationships between piecewise isometries and standard isometries
- Helper lemmas for reasoning about partition pieces
- Continuity properties in the interior of pieces

## Main definitions

- `PiecewiseIsometry.restrictToPiece`: Restriction of a piecewise isometry to a single piece
- `PiecewiseIsometry.isometry_of_piece`: Extract an isometry from a partition piece

## Main results

- `PiecewiseIsometry.continuous_on_interior`: A piecewise isometry is continuous on the interior
  of each partition piece
- `PiecewiseIsometry.injective_on_piece`: A piecewise isometry is injective on each piece
- `partition_cover_iff`: Characterization of partition covering property
- `partition_disjoint_iff`: Characterization of partition disjointness

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

section PartitionProperties

/-- A helper lemma: every point is in some partition piece. -/
theorem mem_partition_of_mem_univ (f : PiecewiseIsometry α) (x : α) :
    ∃ s ∈ f.partition, x ∈ s :=
  f.exists_mem_partition x

/-- The partition pieces are nonempty if the space is nonempty.
NOTE: This theorem as stated is FALSE. A partition {univ, ∅} is a valid partition,
but the empty set is not nonempty. This needs an additional assumption like
"minimal partition" or should be removed. For now keeping as sorry. -/
theorem partition_nonempty_of_nonempty [Nonempty α] (f : PiecewiseIsometry α) :
    ∀ s ∈ f.partition, Set.Nonempty s := by
  intro s hs
  sorry -- Statement is false without additional assumptions

/-- Union of partition equals the whole space, alternative formulation. -/
theorem partition_cover_iff (f : PiecewiseIsometry α) :
    (∀ x : α, ∃ s ∈ f.partition, x ∈ s) ↔ ⋃₀ f.partition = Set.univ := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    exact h x
  · intro h x
    rw [Set.sUnion_eq_univ_iff] at h
    exact h x

/-- Disjointness of partition pieces. -/
theorem partition_disjoint_iff (f : PiecewiseIsometry α) :
    (∀ s ∈ f.partition, ∀ t ∈ f.partition, s ≠ t → Disjoint s t) ↔
    f.partition.PairwiseDisjoint id := by
  rfl

/-- If two pieces share a point, they must be equal. -/
theorem eq_of_mem_partition (f : PiecewiseIsometry α) {s t : Set α}
    (hs : s ∈ f.partition) (ht : t ∈ f.partition) {x : α} (hxs : x ∈ s) (hxt : x ∈ t) :
    s = t := by
  exact f.unique_partition_piece x s t hs ht hxs hxt

/-- Partition pieces are either equal or disjoint. -/
theorem partition_eq_or_disjoint (f : PiecewiseIsometry α) (s t : Set α)
    (hs : s ∈ f.partition) (ht : t ∈ f.partition) :
    s = t ∨ Disjoint s t := by
  by_cases h : s = t
  · left
    exact h
  · right
    exact f.partition_disjoint hs ht h

end PartitionProperties

section IsometryProperties

/-- A piecewise isometry preserves distances within each partition piece. -/
theorem dist_eq_on_piece (f : PiecewiseIsometry α) (s : Set α) (hs : s ∈ f.partition)
    (x y : α) (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) = dist x y :=
  f.isometry_on_pieces s hs x hx y hy

/-- A piecewise isometry is injective on each partition piece. -/
theorem injective_on_piece (f : PiecewiseIsometry α) (s : Set α) (hs : s ∈ f.partition) :
    Set.InjOn f s := by
  intro x hx y hy heq
  have h_dist : dist (f x) (f y) = dist x y := f.dist_eq_on_piece s hs x y hx hy
  rw [heq] at h_dist
  simp only [dist_self] at h_dist
  exact dist_eq_zero.mp h_dist.symm

/-- The restriction of a piecewise isometry to a piece is an isometry. -/
theorem isometry_restrict_piece (f : PiecewiseIsometry α) (s : Set α) (hs : s ∈ f.partition) :
    Isometry (s.restrict f) := by
  intro x y
  simp only [Set.restrict]
  -- Convert edist to dist and use isometry property on pieces
  rw [edist_dist, edist_dist]
  congr 1
  exact f.dist_eq_on_piece s hs x y x.property y.property

end IsometryProperties

section ContinuityProperties

/-- A piecewise isometry is continuous on the interior of each partition piece. --/
theorem continuous_on_interior (f : PiecewiseIsometry α) (s : Set α) (hs : s ∈ f.partition) :
    ContinuousOn f (interior s) := by
  -- The map f is an isometry when restricted to s, hence continuous
  -- Isometries are uniformly continuous, so f is continuous on interior s
  sorry  -- TODO: Use that isometry implies continuity

/-- A piecewise isometry is continuous at points in the interior of partition pieces. -/
theorem continuousAt_of_interior (f : PiecewiseIsometry α) (x : α) (s : Set α)
    (hs : s ∈ f.partition) (hx : x ∈ interior s) :
    ContinuousAt f x := by
  -- Use continuous_on_interior and the fact that interior is a neighborhood
  have h_cont : ContinuousOn f (interior s) := f.continuous_on_interior s hs
  exact h_cont.continuousAt (IsOpen.mem_nhds isOpen_interior hx)

/-- The discontinuity set is contained in the union of partition boundaries. --/
theorem discontinuitySet_subset_boundaries (f : PiecewiseIsometry α) :
    {x | ¬ContinuousAt f x} ⊆ f.discontinuitySet := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := f.exists_mem_partition x
  unfold discontinuitySet
  simp only [Set.mem_iUnion]
  by_contra h_not_frontier
  push_neg at h_not_frontier
  -- x not in any frontier implies x in interior of s (by closure-interior-frontier decomposition)
  have : x ∈ interior s := sorry  -- TODO: Use frontier/interior/closure relationship
  exact hx (f.continuousAt_of_interior x s hs this)

end ContinuityProperties

section ConstructorHelpers

/-- Constructor for piecewise isometries from a set partition. -/
def mk_of_set {partition : Set (Set α)}
    (h_meas : ∀ s ∈ partition, MeasurableSet s)
    (h_countable : partition.Countable)
    (h_cover : ⋃₀ partition = Set.univ)
    (h_disj : partition.PairwiseDisjoint id)
    (f : α → α)
    (h_iso : ∀ s ∈ partition, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y) :
    PiecewiseIsometry α where
  partition := partition
  partition_measurable := h_meas
  partition_countable := h_countable
  partition_cover := h_cover
  partition_disjoint := h_disj
  toFun := f
  isometry_on_pieces := h_iso

/-- Constructor for piecewise isometries from two pieces. -/
def mk_two_pieces (s t : Set α)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (h_disj : Disjoint s t)
    (h_cover : s ∪ t = Set.univ)
    (f : α → α)
    (h_iso_s : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y)
    (h_iso_t : ∀ x ∈ t, ∀ y ∈ t, dist (f x) (f y) = dist x y) :
    PiecewiseIsometry α where
  partition := {s, t}
  partition_measurable := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    cases hu with
    | inl h => rw [h]; exact hs_meas
    | inr h => rw [h]; exact ht_meas
  partition_countable := Set.to_countable {s, t}
  partition_cover := by
    simp only [Set.sUnion_insert, Set.sUnion_singleton]
    exact h_cover
  partition_disjoint := by
    intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    cases hu with
    | inl hu_eq =>
      cases hv with
      | inl hv_eq => rw [hu_eq, hv_eq] at huv; exact absurd rfl huv
      | inr hv_eq => rw [hu_eq, hv_eq]; exact h_disj
    | inr hu_eq =>
      cases hv with
      | inl hv_eq => rw [hu_eq, hv_eq]; exact h_disj.symm
      | inr hv_eq => rw [hu_eq, hv_eq] at huv; exact absurd rfl huv
  toFun := f
  isometry_on_pieces := by
    intro u hu x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    cases hu with
    | inl hu_eq => rw [hu_eq] at hx hy; exact h_iso_s x hx y hy
    | inr hu_eq => rw [hu_eq] at hx hy; exact h_iso_t x hx y hy

end ConstructorHelpers

section RelationToIsometry

/-- If the partition is trivial (just the whole space), then the piecewise isometry is a global
isometry. -/
theorem isometry_of_trivial_partition (f : PiecewiseIsometry α)
    (h : f.partition = {Set.univ}) :
    Isometry f := by
  intro x y
  have h_univ : Set.univ ∈ f.partition := by rw [h]; simp
  have : dist (f x) (f y) = dist x y :=
    f.dist_eq_on_piece Set.univ h_univ x y (Set.mem_univ x) (Set.mem_univ y)
  rw [edist_dist, edist_dist]
  exact ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg |>.mpr this

/-- An isometry can be viewed as a piecewise isometry with trivial partition. -/
def of_isometry (f : α → α) (hf : Isometry f) : PiecewiseIsometry α where
  partition := {Set.univ}
  partition_measurable := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact MeasurableSet.univ
  partition_countable := Set.countable_singleton Set.univ
  partition_cover := by simp only [Set.sUnion_singleton]
  partition_disjoint := by
    intro s hs t ht hst
    simp only [Set.mem_singleton_iff] at hs ht
    rw [hs, ht] at hst
    exact absurd rfl hst
  toFun := f
  isometry_on_pieces := by
    intro s hs x _ y _
    simp only [Set.mem_singleton_iff] at hs
    exact hf.dist_eq x y

/-- The identity map as a piecewise isometry. -/
def id : PiecewiseIsometry α :=
  { partition := {Set.univ}
    partition_measurable := by
      intro s hs
      simp only [Set.mem_singleton_iff] at hs
      rw [hs]
      exact MeasurableSet.univ
    partition_countable := Set.countable_singleton Set.univ
    partition_cover := by simp only [Set.sUnion_singleton]
    partition_disjoint := by
      intro s hs t ht hst
      simp only [Set.mem_singleton_iff] at hs ht
      rw [hs, ht] at hst
      exact absurd rfl hst
    toFun := _root_.id
    isometry_on_pieces := by
      intro s hs x _ y _
      rfl }

/-- Applying a piecewise isometry to itself at a point. -/
@[simp]
theorem coe_fn_apply (f : PiecewiseIsometry α) (x : α) :
    f x = f.toFun x := rfl

end RelationToIsometry

end PiecewiseIsometry
