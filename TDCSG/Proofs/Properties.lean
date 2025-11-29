/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Proofs.Basic

/-!
# Properties of Piecewise Isometries

This file develops basic properties and lemmas for working with piecewise isometries, including:
- Properties of partitions and their measurability
- Relationships between piecewise isometries and standard isometries
- Helper lemmas for reasoning about partition pieces
- Continuity properties in the interior of pieces

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
    f.partition.PairwiseDisjoint _root_.id := by
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
  -- The key insight: f preserves distances on s, so it's uniformly continuous on s
  -- and hence continuous on the interior
  apply Metric.continuousOn_iff.mpr
  intro x hx ε hε
  -- Use that f is an isometry on s to show continuity
  use ε, hε
  intro y hy hxy
  -- Since x, y are in interior s and close enough, they're both in s
  have hxs : x ∈ s := interior_subset hx
  have hys : y ∈ s := interior_subset hy
  -- f preserves distances on s
  rw [f.dist_eq_on_piece s hs y x hys hxs]
  exact hxy

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
  have : x ∈ interior s := by
    -- Use the fact that s \ frontier s = interior s
    rw [← self_diff_frontier s]
    exact ⟨hxs, h_not_frontier s hs⟩
  exact hx (f.continuousAt_of_interior x s hs this)

end ContinuityProperties

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

/-- Applying a piecewise isometry to itself at a point. -/
@[simp]
theorem coe_fn_apply (f : PiecewiseIsometry α) (x : α) :
    f x = f.toFun x := rfl

end RelationToIsometry

end PiecewiseIsometry
