/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.PiecewiseIsometry
import TDCSG.Proofs.Basic
import TDCSG.Proofs.Properties
import TDCSG.Proofs.MeasurePreserving
import TDCSG.Proofs.Composition
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite Piecewise Isometries - Definitions

Core definitions for piecewise isometries with finite partitions.

## Main definitions

* `FinitePiecewiseIsometry α`: A piecewise isometry with a finite partition
* `FinitePiecewiseIsometry.card`: The number of pieces in the partition
* `FinitePiecewiseIsometry.pieces`: The partition as a finite set
* `FinitePiecewiseIsometry.Constructors.mk_of_finset`: Constructor from a Finset
* `FinitePiecewiseIsometry.compF`: Composition of finite piecewise isometries
* `FinitePiecewiseIsometry.iterateF`: Iteration of finite piecewise isometries
* `FinitePiecewiseIsometry.Complexity.complexity`: Combinatorial complexity
* `FinitePiecewiseIsometry.Decidability.piece_of`: Extract partition piece containing a point
* `FiniteMeasurePreservingPiecewiseIsometry`: Finite measure-preserving piecewise isometry
* `FinitePiecewiseIsometry.MeasureTheoretic.toMeasurePreservingPI`: Convert to measure-preserving PI

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

/-- A piecewise isometry with a finite partition. -/
structure FinitePiecewiseIsometry (α : Type u) [MetricSpace α] [MeasurableSpace α]
    extends PiecewiseIsometry α where
  /-- The partition has finitely many pieces. -/
  partition_finite : partition.Finite

namespace FinitePiecewiseIsometry

variable (f : FinitePiecewiseIsometry α)

/-- Coercion to piecewise isometry. -/
instance : Coe (FinitePiecewiseIsometry α) (PiecewiseIsometry α) where
  coe f := f.toPiecewiseIsometry

/-- Allow function application. -/
instance : CoeFun (FinitePiecewiseIsometry α) (fun _ => α → α) where
  coe f := f.toFun

/-- The number of pieces in the partition. -/
noncomputable def card : ℕ :=
  f.partition_finite.toFinset.card

/-- The partition as a finite set. -/
noncomputable def pieces : Finset (Set α) :=
  f.partition_finite.toFinset

namespace Constructors

/-- Construct a finite piecewise isometry from a finite set of pieces. -/
def mk_of_finset (pieces : Finset (Set α))
    (_h_nonempty : pieces.Nonempty)
    (h_meas : ∀ s, s ∈ (pieces : Set (Set α)) → MeasurableSet s)
    (h_cover : ⋃₀ (pieces : Set (Set α)) = Set.univ)
    (h_disj : (pieces : Set (Set α)).PairwiseDisjoint (fun x => x))
    (h_pieces_nonempty : ∀ s ∈ (pieces : Set (Set α)), s.Nonempty)
    (g : α → α)
    (h_iso : ∀ s, s ∈ (pieces : Set (Set α)) →
      ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) = dist x y) :
    FinitePiecewiseIsometry α where
  toPiecewiseIsometry := {
    partition := (pieces : Set (Set α))
    partition_measurable := h_meas
    partition_countable := Finset.countable_toSet pieces
    partition_cover := h_cover
    partition_disjoint := h_disj
    partition_nonempty := h_pieces_nonempty
    toFun := g
    isometry_on_pieces := h_iso
  }
  partition_finite := Finset.finite_toSet pieces

end Constructors

section Composition

/-- Composition of finite piecewise isometries. -/
def compF [OpensMeasurableSpace α] [BorelSpace α] (f g : FinitePiecewiseIsometry α) :
    FinitePiecewiseIsometry α where
  toPiecewiseIsometry := PiecewiseIsometry.comp f.toPiecewiseIsometry g.toPiecewiseIsometry
  partition_finite := by
    unfold PiecewiseIsometry.comp PiecewiseIsometry.refinedPartitionPreimage
    apply Set.Finite.subset
    · exact (g.partition_finite.prod f.partition_finite).image
        (fun (s, t) => s ∩ g.toFun ⁻¹' t)
    · intro u hu
      simp only [Set.mem_setOf_eq] at hu
      obtain ⟨s, hs, t, ht, hu_eq, _⟩ := hu
      rw [Set.mem_image]
      use (s, t)
      constructor
      · exact Set.mem_prod.mpr ⟨hs, ht⟩
      · simp [hu_eq]

end Composition

section Iteration

/-- The nth iterate of a finite piecewise isometry. -/
def iterateF [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) : ℕ → FinitePiecewiseIsometry α
  | 0 => FinitePiecewiseIsometry.Constructors.mk_of_finset {Set.univ}
      (by simp [Finset.Nonempty])
      (by intro s hs; simp [Finset.coe_singleton] at hs; rw [hs]; exact MeasurableSet.univ)
      (by simp [Finset.coe_singleton, Set.sUnion_singleton])
      (by intro s hs t ht hst
          simp [Finset.coe_singleton] at hs ht; rw [hs, ht] at hst; contradiction)
      (by intro s hs; simp [Finset.coe_singleton] at hs; rw [hs]; exact Set.univ_nonempty)
      id
      (by intro s hs x _ y _; rfl)
  | n + 1 => f.compF (iterateF f n)

/-- Notation for iteration. -/
notation:max f "^[" n "]" => iterateF f n

end Iteration

namespace Complexity

/-- Combinatorial complexity: number of pieces in the nth iterate. -/
noncomputable def complexity [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) (n : ℕ) : ℕ :=
  (f.iterateF n).card

end Complexity

namespace Decidability

/-- Membership in partition pieces is decidable when pieces are decidable. -/
noncomputable instance decidable_mem_piece [DecidableEq (Set α)]
    (f : FinitePiecewiseIsometry α) (x : α)
    [∀ s : Set α, Decidable (x ∈ s)] :
    Decidable (∃ s ∈ f.partition, x ∈ s) := by
  have h_equiv : (∃ s ∈ f.partition, x ∈ s) ↔ (∃ s ∈ f.pieces, x ∈ s) := by
    constructor
    · intro ⟨s, hs, hxs⟩
      use s
      constructor
      · exact f.partition_finite.mem_toFinset.mpr hs
      · exact hxs
    · intro ⟨s, hs, hxs⟩
      use s
      constructor
      · exact f.partition_finite.mem_toFinset.mp hs
      · exact hxs
  rw [h_equiv]
  infer_instance

/-- Extract the partition piece containing a given point. -/
noncomputable def piece_of (f : FinitePiecewiseIsometry α) (x : α) :
    {s : Set α // s ∈ f.partition ∧ x ∈ s} :=
  let ⟨s, hs, hxs⟩ := Classical.indefiniteDescription _
    (f.toPiecewiseIsometry.exists_mem_partition x)
  ⟨s, hs, hxs⟩

end Decidability

namespace MeasureTheoretic

variable {μ : MeasureTheory.Measure α}

/-- A finite measure-preserving piecewise isometry. -/
structure FiniteMeasurePreservingPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends FinitePiecewiseIsometry α where
  /-- The underlying function is measurable. -/
  measurable_toFun : Measurable toFun
  /-- The function preserves measure. -/
  measure_preserving : MeasureTheory.MeasurePreserving toFun μ μ

/-- Convert to measure-preserving piecewise isometry. -/
def toMeasurePreservingPI
    (f : FiniteMeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f.toPiecewiseIsometry
  measurable_toFun := f.measurable_toFun
  measure_preserving := f.measure_preserving

end MeasureTheoretic

end FinitePiecewiseIsometry

end PiecewiseIsometry
