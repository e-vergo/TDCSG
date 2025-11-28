/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.PiecewiseIsometry

/-!
# Piecewise Isometries

This file contains theorems and lemmas about piecewise isometries on metric spaces.

## Main results

- `PiecewiseIsometry.discontinuitySet_measurable`: The discontinuity set is measurable
- `PiecewiseIsometry.isometry_on`: A piecewise isometry restricts to an isometry on each piece
- `PiecewiseIsometry.exists_mem_partition`: Every point belongs to some partition piece
- `PiecewiseIsometry.unique_partition_piece`: Each point belongs to exactly one piece

-/

universe u v

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

namespace PiecewiseIsometry

/-- The discontinuity set of a piecewise isometry is measurable. -/
theorem discontinuitySet_measurable [OpensMeasurableSpace α]
    (f : PiecewiseIsometry α) : MeasurableSet (f.discontinuitySet) := by
  unfold discontinuitySet
  apply MeasurableSet.biUnion f.partition_countable
  intro s _
  exact measurableSet_frontier

/-- A piecewise isometry is isometric on each piece of its partition. -/
theorem isometry_on (f : PiecewiseIsometry α) (s : Set α) (hs : s ∈ f.partition) :
    ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y :=
  f.isometry_on_pieces s hs

/-- For any point, there exists a partition piece containing it. -/
theorem exists_mem_partition (f : PiecewiseIsometry α) (x : α) :
    ∃ s ∈ f.partition, x ∈ s := by
  have h := f.partition_cover
  rw [Set.sUnion_eq_univ_iff] at h
  exact h x

/-- Each point belongs to exactly one partition piece. -/
theorem unique_partition_piece (f : PiecewiseIsometry α) (x : α)
    (s t : Set α) (hs : s ∈ f.partition) (ht : t ∈ f.partition)
    (hxs : x ∈ s) (hxt : x ∈ t) : s = t := by
  by_contra h
  have : Disjoint s t := f.partition_disjoint hs ht h
  exact this.ne_of_mem hxs hxt rfl

/-- A partition piece is determined by any interior point. -/
theorem partition_piece_of_interior (f : PiecewiseIsometry α) (x : α) (s : Set α)
    (hs : s ∈ f.partition) (hx : x ∈ interior s) :
    ∀ t ∈ f.partition, x ∈ t → t = s := by
  intro t ht hxt
  exact f.unique_partition_piece x t s ht hs hxt (interior_subset hx)

end PiecewiseIsometry

namespace IsPiecewiseIsometry

/-- Every isometry is a piecewise isometry with the trivial partition. -/
theorem isometry {α : Type u} [MetricSpace α] [MeasurableSpace α]
    {f : α → α} (hf : Isometry f) : IsPiecewiseIsometry f := by
  use {Set.univ}
  constructor
  · intro s hs
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact MeasurableSet.univ
  constructor
  · exact Set.countable_singleton Set.univ
  constructor
  · simp only [Set.sUnion_singleton]
  constructor
  · intro s hs t ht hst
    simp only [Set.mem_singleton_iff] at hs ht
    rw [hs, ht] at hst
    exact absurd rfl hst
  · intro s hs x _ y _
    simp only [Set.mem_singleton_iff] at hs
    exact hf.dist_eq x y

/-- The identity function is a piecewise isometry. -/
theorem identity {α : Type u} [MetricSpace α] [MeasurableSpace α] :
    IsPiecewiseIsometry (id : α → α) :=
  isometry isometry_id

/-- Convert predicate to bundled structure. -/
theorem to_piecewise_isometry {α : Type u} [MetricSpace α] [MeasurableSpace α]
    {f : α → α} (hf : IsPiecewiseIsometry f) :
    ∃ (pi : PiecewiseIsometry α), pi.toFun = f := by
  obtain ⟨partition, h_meas, h_countable, h_cover, h_disj, h_iso⟩ := hf
  -- Remove empty sets from the partition
  let partition' := partition \ {∅}
  use {
    partition := partition'
    partition_measurable := by
      intro s hs
      exact h_meas s hs.1
    partition_countable := h_countable.mono Set.diff_subset
    partition_cover := by
      rw [Set.sUnion_diff_singleton_empty]
      exact h_cover
    partition_disjoint := by
      intro s hs t ht hst
      exact h_disj hs.1 ht.1 hst
    partition_nonempty := by
      intro s hs
      -- s ∈ partition' means s ∈ partition and s ≠ ∅
      rw [Set.mem_diff, Set.mem_singleton_iff] at hs
      exact Set.nonempty_iff_ne_empty.mpr hs.2
    toFun := f
    isometry_on_pieces := by
      intro s hs x hxs y hys
      exact h_iso s hs.1 x hxs y hys
  }

end IsPiecewiseIsometry
