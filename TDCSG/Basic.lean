/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Separation.Hausdorff

/-!
# Piecewise Isometries

In this file we define piecewise isometries on metric spaces.

## Main definitions

- `PiecewiseIsometry`: A map on a metric space that restricts to an isometry on each piece
  of a measurable partition
- `PiecewiseIsometry.discontinuitySet`: The set of discontinuities
- `IsPiecewiseIsometry`: A predicate asserting that a function is a piecewise isometry

## Main results

- `PiecewiseIsometry.discontinuitySet_measurable`: The discontinuity set is measurable
- `PiecewiseIsometry.isometry_on`: A piecewise isometry restricts to an isometry on each piece

-/

universe u v

/-- A piecewise isometry on a metric space with a measurable partition. -/
structure PiecewiseIsometry (α : Type u) [MetricSpace α] [MeasurableSpace α] where
  /-- The partition pieces of the domain -/
  partition : Set (Set α)
  /-- Each piece in the partition is measurable -/
  partition_measurable : ∀ s ∈ partition, MeasurableSet s
  /-- The partition pieces cover the entire space -/
  partition_cover : ⋃₀ partition = Set.univ
  /-- The partition pieces are pairwise disjoint -/
  partition_disjoint : partition.PairwiseDisjoint id
  /-- The underlying function -/
  toFun : α → α
  /-- The function is isometric when restricted to each piece -/
  isometry_on_pieces : ∀ s ∈ partition, ∀ x ∈ s, ∀ y ∈ s,
    dist (toFun x) (toFun y) = dist x y

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

namespace PiecewiseIsometry

/-- Allow function application notation for piecewise isometries -/
instance : CoeFun (PiecewiseIsometry α) (fun _ => α → α) where
  coe f := f.toFun

/-- The set of potential discontinuities of a piecewise isometry. -/
def discontinuitySet (f : PiecewiseIsometry α) : Set α :=
  ⋃ s ∈ f.partition, frontier s

/-- The discontinuity set of a piecewise isometry is measurable. -/
theorem discontinuitySet_measurable [T2Space α] (f : PiecewiseIsometry α) :
    MeasurableSet (f.discontinuitySet) := by
  unfold discontinuitySet
  sorry  -- Need countability or finite union assumption

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

/-- A predicate asserting that a function is a piecewise isometry. -/
def IsPiecewiseIsometry {α : Type u} [MetricSpace α] [MeasurableSpace α] (f : α → α) : Prop :=
  ∃ (partition : Set (Set α)),
    (∀ s ∈ partition, MeasurableSet s) ∧
    (⋃₀ partition = Set.univ) ∧
    (partition.PairwiseDisjoint id) ∧
    (∀ s ∈ partition, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y)

namespace IsPiecewiseIsometry

/-- Every isometry is a piecewise isometry with the trivial partition. -/
theorem of_isometry {α : Type u} [MetricSpace α] [MeasurableSpace α]
    {f : α → α} (hf : Isometry f) : IsPiecewiseIsometry f := by
  use {Set.univ}
  constructor
  · intro s hs
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact MeasurableSet.univ
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
theorem id {α : Type u} [MetricSpace α] [MeasurableSpace α] :
    IsPiecewiseIsometry (id : α → α) :=
  of_isometry isometry_id

/-- Convert predicate to bundled structure. -/
theorem to_piecewise_isometry {α : Type u} [MetricSpace α] [MeasurableSpace α]
    {f : α → α} (hf : IsPiecewiseIsometry f) :
    ∃ (pi : PiecewiseIsometry α), pi.toFun = f := by
  obtain ⟨partition, h_meas, h_cover, h_disj, h_iso⟩ := hf
  use {
    partition := partition
    partition_measurable := h_meas
    partition_cover := h_cover
    partition_disjoint := h_disj
    toFun := f
    isometry_on_pieces := h_iso
  }

end IsPiecewiseIsometry
