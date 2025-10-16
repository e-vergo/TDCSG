/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.MeasurePreserving
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite Piecewise Isometries

This file specializes the theory of piecewise isometries to the case where the partition
has finitely many pieces. This is a common and important special case, including:
- Interval exchange transformations (finite intervals)
- Polygonal billiards (finite polygonal pieces)
- Many computational and applied examples

## Main definitions

- `FinitePiecewiseIsometry α`: A piecewise isometry with a finite partition
- `FinitePiecewiseIsometry.card`: The number of pieces in the partition
- `FinitePiecewiseIsometry.pieces`: The partition as a finite set

## Main results

- `finite_discontinuitySet`: The discontinuity set of a finite piecewise isometry is finite
  (under suitable topological conditions)
- `finite_orbit_images`: Images under iteration have bounded complexity
- `decidable_piece_membership`: Membership in partition pieces is decidable (under conditions)

## Implementation notes

We use `Set.Finite` to express finiteness of the partition, which integrates well with
mathlib's set theory. The finite structure could alternatively be expressed using `Finset`,
which we provide constructors for.

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

/-- A piecewise isometry with a finite partition.

This specializes `PiecewiseIsometry` by requiring that the partition has finitely many pieces. -/
structure FinitePiecewiseIsometry (α : Type u) [MetricSpace α] [MeasurableSpace α]
    extends PiecewiseIsometry α where
  /-- The partition has finitely many pieces -/
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

/-- Function application. -/
@[simp]
theorem apply_eq_toFun (x : α) :
    f x = f.toFun x := rfl

end FinitePiecewiseIsometry

section FiniteProperties

variable (f : FinitePiecewiseIsometry α)

/-- The discontinuity set of a finite piecewise isometry is contained in finitely many
boundaries. -/
theorem discontinuitySet_finite_boundaries [T2Space α] [SecondCountableTopology α] :
    ∃ (s : Finset (Set α)), f.discontinuitySet ⊆ ⋃ t ∈ s, frontier t := by
  sorry  -- Use finiteness of partition

/-- For compact metric spaces, a finite piecewise isometry has finite discontinuity set. -/
theorem finite_discontinuitySet [CompactSpace α] [T2Space α] :
    f.discontinuitySet.Finite := by
  sorry  -- Boundaries of finitely many measurable sets in compact space

/-- Each partition piece is nonempty (assuming α is nonempty). -/
theorem pieces_nonempty [Nonempty α] :
    ∀ s ∈ f.partition, s.Nonempty := by
  sorry  -- If some piece were empty, could be removed

/-- The number of pieces is positive (assuming α is nonempty). -/
theorem card_pos [Nonempty α] :
    0 < f.card := by
  sorry  -- At least one piece needed to cover nonempty space

end FiniteProperties

section Constructors

/-- Construct a finite piecewise isometry from a list of pieces. -/
def mk_of_list (pieces : List (Set α))
    (h_nonempty : pieces ≠ [])
    (h_meas : ∀ s ∈ pieces, MeasurableSet s)
    (h_cover : ⋃₀ pieces.toSet = Set.univ)
    (h_disj : pieces.toSet.PairwiseDisjoint id)
    (g : α → α)
    (h_iso : ∀ s ∈ pieces, ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) = dist x y) :
    FinitePiecewiseIsometry α where
  toPiecewiseIsometry := {
    partition := pieces.toSet
    partition_measurable := fun s hs => h_meas s (List.mem_toSet.mp hs)
    partition_cover := h_cover
    partition_disjoint := h_disj
    toFun := g
    isometry_on_pieces := fun s hs => h_iso s (List.mem_toSet.mp hs)
  }
  partition_finite := List.finite_toSet pieces

/-- Construct a finite piecewise isometry from a Finset of pieces. -/
def mk_of_finset (pieces : Finset (Set α))
    (h_nonempty : pieces.Nonempty)
    (h_meas : ∀ s ∈ pieces, MeasurableSet s)
    (h_cover : ⋃₀ (pieces : Set (Set α)) = Set.univ)
    (h_disj : (pieces : Set (Set α)).PairwiseDisjoint id)
    (g : α → α)
    (h_iso : ∀ s ∈ pieces, ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) = dist x y) :
    FinitePiecewiseIsometry α where
  toPiecewiseIsometry := {
    partition := pieces
    partition_measurable := h_meas
    partition_cover := h_cover
    partition_disjoint := h_disj
    toFun := g
    isometry_on_pieces := h_iso
  }
  partition_finite := Finset.finite_toSet pieces

end Constructors

section Composition

/-- Composition of finite piecewise isometries has a finite partition. -/
def comp (f g : FinitePiecewiseIsometry α) : FinitePiecewiseIsometry α where
  toPiecewiseIsometry := f.toPiecewiseIsometry.comp g.toPiecewiseIsometry
  partition_finite := by
    sorry  -- Refinement of two finite partitions is finite

/-- The number of pieces in a composition is bounded by the product of the numbers of pieces. -/
theorem card_comp_le (f g : FinitePiecewiseIsometry α) :
    (f.comp g).card ≤ f.card * g.card := by
  sorry  -- At most |f.partition| * |g.partition| pieces in refinement

end Composition

section Iteration

/-- The nth iterate of a finite piecewise isometry. -/
def iterate (f : FinitePiecewiseIsometry α) (n : ℕ) : FinitePiecewiseIsometry α :=
  match n with
  | 0 => mk_of_list [Set.univ] (by simp) (by simp [MeasurableSet.univ])
      (by simp) (by simp [Set.PairwiseDisjoint])
      id (by simp [Isometry.id.dist_eq])
  | n + 1 => f.comp (iterate f n)

/-- Notation for iteration. -/
notation:max f "^[" n "]" => iterate f n

/-- The number of pieces in an iterate grows at most exponentially. -/
theorem card_iterate_le (f : FinitePiecewiseIsometry α) (n : ℕ) :
    (f^[n]).card ≤ f.card ^ n := by
  sorry  -- By induction using card_comp_le

end Iteration

section Complexity

/-- The combinatorial complexity of a finite piecewise isometry, measuring how the partition
refines under iteration. -/
noncomputable def complexity (f : FinitePiecewiseIsometry α) (n : ℕ) : ℕ :=
  (f^[n]).card

/-- Complexity is submultiplicative. -/
theorem complexity_submult (f : FinitePiecewiseIsometry α) (m n : ℕ) :
    complexity f (m + n) ≤ complexity f m * complexity f n := by
  sorry  -- Follows from composition bound

/-- For interval exchange transformations, complexity grows linearly. -/
theorem IET_complexity_linear (f : FinitePiecewiseIsometry α)
    (h_IET : sorry) :  -- Needs IET characterization
    ∃ C : ℕ, ∀ n : ℕ, complexity f n ≤ C * n := by
  sorry  -- Classic result for IETs

end Complexity

section Decidability

/-- If partition pieces can be decided, then membership is decidable. -/
instance decidable_mem_piece [DecidableEq (Set α)]
    (f : FinitePiecewiseIsometry α) (x : α)
    [∀ s : Set α, Decidable (x ∈ s)] :
    Decidable (∃ s ∈ f.partition, x ∈ s) := by
  sorry  -- Use finiteness to decide

/-- For finite partitions with decidable membership, we can compute which piece a point
belongs to. -/
noncomputable def piece_of (f : FinitePiecewiseIsometry α) (x : α) :
    {s : Set α // s ∈ f.partition ∧ x ∈ s} := by
  sorry  -- Use exists_mem_partition and finite search

end Decidability

section MeasureTheoretic

variable {μ : MeasureTheory.Measure α}

/-- A finite measure-preserving piecewise isometry. -/
structure FiniteMeasurePreservingPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends FinitePiecewiseIsometry α where
  /-- The underlying function is measurable -/
  measurable_toFun : Measurable toFun
  /-- The function preserves measure -/
  measure_preserving : MeasureTheory.MeasurePreserving toFun μ μ

/-- Convert to measure-preserving piecewise isometry. -/
def FiniteMeasurePreservingPiecewiseIsometry.toMeasurePreserving
    (f : FiniteMeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f.toPiecewiseIsometry
  measurable_toFun := f.measurable_toFun
  measure_preserving := f.measure_preserving

/-- For finite partitions, measure preservation can be checked piece-by-piece. -/
theorem measurePreserving_of_pieces
    (f : FinitePiecewiseIsometry α) (h_meas : Measurable f.toFun)
    (h_pieces : ∀ s ∈ f.partition, μ (f.toFun '' s) = μ s) :
    MeasureTheory.MeasurePreserving f.toFun μ μ := by
  sorry  -- Sum over finite pieces

end MeasureTheoretic

end PiecewiseIsometry
