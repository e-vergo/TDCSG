/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.MeasurePreserving
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite Piecewise Isometries

Theory of piecewise isometries with finite partitions.

## Main definitions

* `FinitePiecewiseIsometry α`: A piecewise isometry with a finite partition
* `FinitePiecewiseIsometry.card`: The number of pieces in the partition
* `FinitePiecewiseIsometry.pieces`: The partition as a finite set

## Main results

* `finite_discontinuitySet_of_discrete`: Discontinuity sets are finite in discrete spaces
* `card_iterate_le`: Complexity grows at most exponentially under iteration
* `complexity_linear_of_bounded_refinement`: Linear complexity for bounded refinement
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

/-- Function application. -/
@[simp]
theorem apply_eq_toFun (x : α) :
    f x = f.toFun x := rfl

section FiniteProperties

/-- The discontinuity set is contained in finitely many boundaries. -/
theorem discontinuitySet_finite_boundaries [T2Space α] [SecondCountableTopology α] :
    ∃ (s : Finset (Set α)), f.discontinuitySet ⊆ ⋃ t ∈ s, frontier t := by
  -- The discontinuity set is the union of frontiers of partition pieces
  use f.pieces
  intro x hx
  unfold discontinuitySet at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  simp only [Set.mem_iUnion, exists_prop]
  use t
  constructor
  · exact f.partition_finite.mem_toFinset.mpr ht
  · exact hxt

/-- In a discrete space, the discontinuity set is finite. -/
theorem finite_discontinuitySet_of_discrete [CompactSpace α] [T2Space α] [DiscreteTopology α] :
    f.discontinuitySet.Finite := by
  have h_frontier_empty : ∀ s : Set α, frontier s = ∅ := by
    intro s
    rw [frontier, closure_discrete, (isOpen_discrete s).interior_eq, Set.diff_self]
  obtain ⟨finset_pieces, h_subset⟩ := f.discontinuitySet_finite_boundaries
  have h_union_empty : ⋃ t ∈ finset_pieces, frontier t = ∅ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
    intro ⟨t, _, hx⟩
    rw [h_frontier_empty t] at hx
    exact hx
  have : f.discontinuitySet ⊆ ∅ := by
    calc f.discontinuitySet ⊆ ⋃ t ∈ finset_pieces, frontier t := h_subset
       _ = ∅ := h_union_empty
  exact Set.Finite.subset (Set.finite_empty) this

/-- The number of pieces is positive for nonempty spaces. -/
theorem card_pos [Nonempty α] :
    0 < f.card := by
  unfold card
  rw [Finset.card_pos]
  rw [Finset.nonempty_iff_ne_empty]
  intro h_empty
  have h_partition_empty : f.partition = ∅ := by
    ext s
    constructor
    · intro hs
      have : s ∈ f.partition_finite.toFinset := f.partition_finite.mem_toFinset.mpr hs
      rw [h_empty] at this
      exact Finset.notMem_empty s this
    · intro hs
      exact absurd hs (Set.notMem_empty s)
  have h_cover := f.partition_cover
  rw [h_partition_empty] at h_cover
  simp only [Set.sUnion_empty] at h_cover
  obtain ⟨x⟩ := ‹Nonempty α›
  have : x ∈ (Set.univ : Set α) := Set.mem_univ x
  rw [← h_cover] at this
  exact this

end FiniteProperties

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

end FinitePiecewiseIsometry

namespace FinitePiecewiseIsometry

section Composition

/-- Composition of finite piecewise isometries. -/
def comp [OpensMeasurableSpace α] [BorelSpace α] (f g : FinitePiecewiseIsometry α) :
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

/-- Composition increases complexity at most multiplicatively. -/
theorem card_comp_le [OpensMeasurableSpace α] [BorelSpace α] (f g : FinitePiecewiseIsometry α) :
    (f.comp g).card ≤ f.card * g.card := by
  unfold card comp
  simp only
  have h_subset : (f.comp g).partition ⊆
      (fun (st : Set α × Set α) => st.1 ∩ g.toFun ⁻¹' st.2) ''
        (g.partition ×ˢ f.partition) := by
    intro u hu
    unfold comp PiecewiseIsometry.comp PiecewiseIsometry.refinedPartitionPreimage at hu
    simp only [Set.mem_setOf_eq] at hu
    obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
    use (s, t)
    simp [Set.mem_prod, hs, ht]
  have h_card_le : (partition_finite (comp f g)).toFinset.card ≤
      ((g.partition_finite.prod f.partition_finite).image
        (fun st => st.1 ∩ g.toFun ⁻¹' st.2)).toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Set.Finite.mem_toFinset] at hx ⊢
    exact h_subset hx
  have h_image_card : ((g.partition_finite.prod f.partition_finite).image
      (fun st => st.1 ∩ g.toFun ⁻¹' st.2)).toFinset.card ≤
      (g.partition_finite.prod f.partition_finite).toFinset.card := by
    classical
    have h_finite_prod : (g.partition ×ˢ f.partition).Finite :=
      g.partition_finite.prod f.partition_finite
    rw [Set.Finite.toFinset_image _ h_finite_prod]
    apply Finset.card_image_le
  have h_prod_card : (g.partition_finite.prod f.partition_finite).toFinset.card =
      g.partition_finite.toFinset.card * f.partition_finite.toFinset.card := by
    classical
    have : (g.partition_finite.prod f.partition_finite).toFinset =
      g.partition_finite.toFinset ×ˢ f.partition_finite.toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_prod, Finset.mem_product]
    rw [this]
    exact Finset.card_product _ _
  calc (partition_finite (comp f g)).toFinset.card
      ≤ ((g.partition_finite.prod f.partition_finite).image
          (fun st => st.1 ∩ g.toFun ⁻¹' st.2)).toFinset.card := h_card_le
    _ ≤ (g.partition_finite.prod f.partition_finite).toFinset.card := h_image_card
    _ = g.partition_finite.toFinset.card * f.partition_finite.toFinset.card :=
        h_prod_card
    _ = f.card * g.card := by unfold card; ring

end Composition

section Iteration

/-- The nth iterate of a finite piecewise isometry. -/
def iterate [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
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
  | n + 1 => f.comp (iterate f n)

/-- Complexity of iteration grows at most exponentially. -/
theorem card_iterate_le [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) (n : ℕ) :
    (iterate f n).card ≤ f.card ^ n := by
  induction n with
  | zero =>
    unfold iterate card
    simp only [pow_zero]
    show (Finset.finite_toSet {Set.univ}).toFinset.card ≤ 1
    simp [Finset.card_singleton]
  | succ n ih =>
    calc (iterate f (n + 1)).card
        = (f.comp (iterate f n)).card := rfl
      _ ≤ f.card * (iterate f n).card := card_comp_le f (iterate f n)
      _ ≤ f.card * f.card ^ n := Nat.mul_le_mul_left f.card ih
      _ = f.card ^ (n + 1) := by ring

/-- Notation for iteration. -/
notation:max f "^[" n "]" => iterate f n

end Iteration

namespace Complexity

/-- Combinatorial complexity: number of pieces in the nth iterate. -/
noncomputable def complexity [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) (n : ℕ) : ℕ :=
  (f.iterate n).card

/-- Complexity grows at most exponentially. -/
theorem complexity_exponential_bound [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) (n : ℕ) :
    complexity f n ≤ f.card ^ n := by
  unfold complexity
  exact card_iterate_le f n

/-- Complexity grows linearly when refinement is bounded. -/
theorem complexity_linear_of_bounded_refinement [Nonempty α] [OpensMeasurableSpace α]
    [BorelSpace α] (f : FinitePiecewiseIsometry α) (C : ℕ)
    (h_card : 1 ≤ f.card)
    (h_bounded : ∀ m : ℕ, (f.iterate (m + 1)).card ≤ (f.iterate m).card + C) :
    ∀ n : ℕ, complexity f n ≤ f.card + n * C := by
  intro n
  unfold complexity
  induction n with
  | zero =>
    simp only [Nat.zero_mul, add_zero]
    have h0 : (f.iterate 0).card = 1 := by
      unfold iterate card
      simp only [Constructors.mk_of_finset]
      show (Finset.finite_toSet {Set.univ}).toFinset.card = 1
      rw [Finset.finite_toSet_toFinset]
      exact Finset.card_singleton Set.univ
    rw [h0]
    exact h_card
  | succ n ih =>
    calc (f.iterate (n + 1)).card
        ≤ (f.iterate n).card + C := h_bounded n
      _ ≤ (f.card + n * C) + C := Nat.add_le_add_right ih C
      _ = f.card + (n * C + C) := by ring
      _ = f.card + (n + 1) * C := by ring

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
def FiniteMeasurePreservingPiecewiseIsometry.toMeasurePreserving
    (f : FiniteMeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f.toPiecewiseIsometry
  measurable_toFun := f.measurable_toFun
  measure_preserving := f.measure_preserving

end MeasureTheoretic

end FinitePiecewiseIsometry

end PiecewiseIsometry
