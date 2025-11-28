/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Piecewise Isometry Definitions

This file contains the core definitions for piecewise isometries on metric spaces.

## Main definitions

- `PiecewiseIsometry`: A map on a metric space that restricts to an isometry on each piece
  of a measurable partition
- `PiecewiseIsometry.discontinuitySet`: The set of potential discontinuities
- `IsPiecewiseIsometry`: A predicate asserting that a function is a piecewise isometry
- `PiecewiseIsometry.mk_of_set`: Constructor from a set partition
- `PiecewiseIsometry.mk_two_pieces`: Constructor from two pieces
- `PiecewiseIsometry.of_isometry`: Convert an isometry to a piecewise isometry
- `PiecewiseIsometry.id`: The identity as a piecewise isometry
-/

universe u v

/-- A piecewise isometry on a metric space with a measurable partition. -/
structure PiecewiseIsometry (α : Type u) [MetricSpace α] [MeasurableSpace α] where
  /-- The partition pieces of the domain -/
  partition : Set (Set α)
  /-- Each piece in the partition is measurable -/
  partition_measurable : ∀ s ∈ partition, MeasurableSet s
  /-- The partition is countable -/
  partition_countable : partition.Countable
  /-- The partition pieces cover the entire space -/
  partition_cover : ⋃₀ partition = Set.univ
  /-- The partition pieces are pairwise disjoint -/
  partition_disjoint : partition.PairwiseDisjoint id
  /-- Each partition piece is nonempty -/
  partition_nonempty : ∀ s ∈ partition, s.Nonempty
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

/-- Constructor for piecewise isometries from a set partition. -/
def mk_of_set {partition : Set (Set α)}
    (h_meas : ∀ s ∈ partition, MeasurableSet s)
    (h_countable : partition.Countable)
    (h_cover : ⋃₀ partition = Set.univ)
    (h_disj : partition.PairwiseDisjoint id)
    (h_nonempty : ∀ s ∈ partition, s.Nonempty)
    (f : α → α)
    (h_iso : ∀ s ∈ partition, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y) :
    PiecewiseIsometry α where
  partition := partition
  partition_measurable := h_meas
  partition_countable := h_countable
  partition_cover := h_cover
  partition_disjoint := h_disj
  partition_nonempty := h_nonempty
  toFun := f
  isometry_on_pieces := h_iso

/-- Constructor for piecewise isometries from two pieces. -/
def mk_two_pieces (s t : Set α)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (hs_nonempty : s.Nonempty) (ht_nonempty : t.Nonempty)
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
  partition_nonempty := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    cases hu with
    | inl h => rw [h]; exact hs_nonempty
    | inr h => rw [h]; exact ht_nonempty
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

/-- An isometry can be viewed as a piecewise isometry with trivial partition. -/
def of_isometry (f : α → α) [Nonempty α] (hf : Isometry f) : PiecewiseIsometry α where
  partition := {Set.univ}
  partition_measurable := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact MeasurableSet.univ
  partition_countable := Set.countable_singleton Set.univ
  partition_cover := by simp only [Set.sUnion_singleton]
  partition_nonempty := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact Set.univ_nonempty
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
def id [Nonempty α] : PiecewiseIsometry α :=
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
    partition_nonempty := by
      intro s hs
      simp only [Set.mem_singleton_iff] at hs
      rw [hs]
      exact Set.univ_nonempty
    toFun := _root_.id
    isometry_on_pieces := by
      intro s hs x _ y _
      rfl }

end PiecewiseIsometry

/-- A predicate asserting that a function is a piecewise isometry. -/
def IsPiecewiseIsometry {α : Type u} [MetricSpace α] [MeasurableSpace α] (f : α → α) : Prop :=
  ∃ (partition : Set (Set α)),
    (∀ s ∈ partition, MeasurableSet s) ∧
    (partition.Countable) ∧
    (⋃₀ partition = Set.univ) ∧
    (partition.PairwiseDisjoint id) ∧
    (∀ s ∈ partition, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y)
