/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.Finite

/-!
# Finite Piecewise Isometries - Theorems

Theory of piecewise isometries with finite partitions.

## Main results

* `finite_discontinuitySet_of_discrete`: Discontinuity sets are finite in discrete spaces
* `card_iterate_le`: Complexity grows at most exponentially under iteration
* `complexity_linear_of_bounded_refinement`: Linear complexity for bounded refinement
-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

namespace FinitePiecewiseIsometry

variable (f : FinitePiecewiseIsometry α)

/-- Function application. -/
@[simp]
theorem finite_apply (x : α) :
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

section Composition

/-- Composition increases complexity at most multiplicatively. -/
theorem card_compF_le [OpensMeasurableSpace α] [BorelSpace α] (f g : FinitePiecewiseIsometry α) :
    (f.compF g).card ≤ f.card * g.card := by
  unfold card compF
  simp only
  have h_subset : (f.compF g).partition ⊆
      (fun (st : Set α × Set α) => st.1 ∩ g.toFun ⁻¹' st.2) ''
        (g.partition ×ˢ f.partition) := by
    intro u hu
    unfold compF PiecewiseIsometry.comp PiecewiseIsometry.refinedPartitionPreimage at hu
    simp only [Set.mem_setOf_eq] at hu
    obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
    use (s, t)
    simp [Set.mem_prod, hs, ht]
  have h_card_le : (partition_finite (compF f g)).toFinset.card ≤
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
  calc (partition_finite (compF f g)).toFinset.card
      ≤ ((g.partition_finite.prod f.partition_finite).image
          (fun st => st.1 ∩ g.toFun ⁻¹' st.2)).toFinset.card := h_card_le
    _ ≤ (g.partition_finite.prod f.partition_finite).toFinset.card := h_image_card
    _ = g.partition_finite.toFinset.card * f.partition_finite.toFinset.card :=
        h_prod_card
    _ = f.card * g.card := by unfold card; ring

end Composition

section Iteration

/-- Complexity of iteration grows at most exponentially. -/
theorem card_iterateF_le [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) (n : ℕ) :
    (iterateF f n).card ≤ f.card ^ n := by
  induction n with
  | zero =>
    unfold iterateF card
    simp only [pow_zero]
    show (Finset.finite_toSet {Set.univ}).toFinset.card ≤ 1
    simp [Finset.card_singleton]
  | succ n ih =>
    calc (iterateF f (n + 1)).card
        = (f.compF (iterateF f n)).card := rfl
      _ ≤ f.card * (iterateF f n).card := card_compF_le f (iterateF f n)
      _ ≤ f.card * f.card ^ n := Nat.mul_le_mul_left f.card ih
      _ = f.card ^ (n + 1) := by ring

end Iteration

namespace Complexity

/-- Complexity grows at most exponentially. -/
theorem complexity_exponential_bound [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : FinitePiecewiseIsometry α) (n : ℕ) :
    complexity f n ≤ f.card ^ n := by
  unfold complexity
  exact card_iterateF_le f n

/-- Complexity grows linearly when refinement is bounded. -/
theorem complexity_linear_of_bounded_refinement [Nonempty α] [OpensMeasurableSpace α]
    [BorelSpace α] (f : FinitePiecewiseIsometry α) (C : ℕ)
    (h_card : 1 ≤ f.card)
    (h_bounded : ∀ m : ℕ, (f.iterateF (m + 1)).card ≤ (f.iterateF m).card + C) :
    ∀ n : ℕ, complexity f n ≤ f.card + n * C := by
  intro n
  unfold complexity
  induction n with
  | zero =>
    simp only [Nat.zero_mul, add_zero]
    have h0 : (f.iterateF 0).card = 1 := by
      unfold iterateF card
      simp only [Constructors.mk_of_finset]
      show (Finset.finite_toSet {Set.univ}).toFinset.card = 1
      rw [Finset.finite_toSet_toFinset]
      exact Finset.card_singleton Set.univ
    rw [h0]
    exact h_card
  | succ n ih =>
    calc (f.iterateF (n + 1)).card
        ≤ (f.iterateF n).card + C := h_bounded n
      _ ≤ (f.card + n * C) + C := Nat.add_le_add_right ih C
      _ = f.card + (n * C + C) := by ring
      _ = f.card + (n + 1) * C := by ring

end Complexity

end FinitePiecewiseIsometry

end PiecewiseIsometry
