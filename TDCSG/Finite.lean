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

section FiniteProperties

/-- The discontinuity set of a finite piecewise isometry is contained in finitely many
boundaries. -/
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

/-- For compact metric spaces with discrete topology, a finite piecewise isometry has finite
discontinuity set.

The discontinuity set is a finite union of frontiers (by `discontinuitySet_finite_boundaries`).
In a discrete space, each frontier is empty, so the discontinuity set is empty, hence finite.

For more general spaces, this requires additional hypotheses such as:
- The partition pieces are polytopes or similar (finite boundary)
- Each frontier is finite (e.g., in ℝⁿ with polytopic partitions)

This version with `DiscreteTopology` is provable and covers computational examples. -/
theorem finite_discontinuitySet_of_discrete [CompactSpace α] [T2Space α] [DiscreteTopology α] :
    f.discontinuitySet.Finite := by
  -- In a discrete space, every set equals its interior union its frontier
  -- For any set s, frontier s = closure s \ interior s
  -- In discrete topology, interior s = s and closure s = s, so frontier s = s \ s = ∅
  have h_frontier_empty : ∀ s : Set α, frontier s = ∅ := by
    intro s
    rw [frontier, closure_discrete, (isOpen_discrete s).interior_eq, Set.diff_self]
  -- Discontinuity set is contained in union of frontiers
  obtain ⟨finset_pieces, h_subset⟩ := f.discontinuitySet_finite_boundaries
  -- Each frontier is empty, so the union is empty
  have h_union_empty : ⋃ t ∈ finset_pieces, frontier t = ∅ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
    intro ⟨t, _, hx⟩
    rw [h_frontier_empty t] at hx
    exact hx
  -- Therefore discontinuity set is subset of empty, hence empty, hence finite
  have : f.discontinuitySet ⊆ ∅ := by
    calc f.discontinuitySet ⊆ ⋃ t ∈ finset_pieces, frontier t := h_subset
       _ = ∅ := h_union_empty
  exact Set.Finite.subset (Set.finite_empty) this

/-- The number of pieces is positive (assuming α is nonempty). -/
theorem card_pos [Nonempty α] :
    0 < f.card := by
  -- The partition must be nonempty to cover a nonempty space
  unfold card
  rw [Finset.card_pos]
  -- Show f.partition_finite.toFinset is nonempty
  rw [Finset.nonempty_iff_ne_empty]
  intro h_empty
  -- If toFinset is empty, then partition is empty
  have h_partition_empty : f.partition = ∅ := by
    ext s
    constructor
    · intro hs
      have : s ∈ f.partition_finite.toFinset := f.partition_finite.mem_toFinset.mpr hs
      rw [h_empty] at this
      exact Finset.notMem_empty s this
    · intro hs
      exact absurd hs (Set.notMem_empty s)
  -- But partition covers univ, so univ = ∅
  have h_cover := f.partition_cover
  rw [h_partition_empty] at h_cover
  simp only [Set.sUnion_empty] at h_cover
  -- This contradicts α being nonempty
  obtain ⟨x⟩ := ‹Nonempty α›
  have : x ∈ (Set.univ : Set α) := Set.mem_univ x
  rw [← h_cover] at this
  exact this

end FiniteProperties

namespace Constructors

/-- Construct a finite piecewise isometry from a Finset of pieces. -/
def mk_of_finset (pieces : Finset (Set α))
    (_h_nonempty : pieces.Nonempty)
    (h_meas : ∀ s, s ∈ (pieces : Set (Set α)) → MeasurableSet s)
    (h_cover : ⋃₀ (pieces : Set (Set α)) = Set.univ)
    (h_disj : (pieces : Set (Set α)).PairwiseDisjoint (fun x => x))
    (h_pieces_nonempty : ∀ s ∈ (pieces : Set (Set α)), s.Nonempty)
    (g : α → α)
    (h_iso : ∀ s, s ∈ (pieces : Set (Set α)) → ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) = dist x y) :
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

/-- Composition of finite piecewise isometries has a finite partition. -/
def comp (f g : FinitePiecewiseIsometry α) : FinitePiecewiseIsometry α where
  toPiecewiseIsometry := PiecewiseIsometry.comp f.toPiecewiseIsometry g.toPiecewiseIsometry
  partition_finite := by
    -- The refined partition is a subset of the image of f.partition × g.partition
    -- under the intersection operation, which is finite since both partitions are finite
    unfold PiecewiseIsometry.comp PiecewiseIsometry.refinedPartition
    apply Set.Finite.subset
    · exact (f.partition_finite.prod g.partition_finite).image (fun (s, t) => s ∩ t)
    · intro u hu
      -- Show u is in the image
      -- hu tells us u ∈ {u | ∃ s ∈ g.partition, ∃ t ∈ f.partition, u = s ∩ t ∧ (s ∩ t).Nonempty}
      simp only [Set.mem_setOf_eq] at hu
      obtain ⟨s, hs, t, ht, hu_eq, _⟩ := hu
      rw [Set.mem_image]
      use (t, s)
      constructor
      · exact Set.mem_prod.mpr ⟨ht, hs⟩
      · simp [hu_eq, Set.inter_comm]

/-- The number of pieces in a composition is bounded by the product of the numbers of pieces. -/
theorem card_comp_le (f g : FinitePiecewiseIsometry α) :
    (f.comp g).card ≤ f.card * g.card := by
  -- The refined partition has at most |f.partition| * |g.partition| pieces
  unfold card comp
  simp only
  -- The partition of comp is refinedPartition, which is a subset of the image
  -- We use that card of finite set ≤ card of finite superset
  have h_subset : PiecewiseIsometry.refinedPartition g.partition f.partition ⊆
      (fun (st : Set α × Set α) => st.1 ∩ st.2) '' (f.partition ×ˢ g.partition) := by
    intro u hu
    unfold PiecewiseIsometry.refinedPartition at hu
    simp only [Set.mem_setOf_eq] at hu
    obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
    use (t, s)
    simp [Set.mem_prod, ht, hs, Set.inter_comm]
  -- Now use that card of subset ≤ card of superset
  -- The refined partition is finite and is a subset of the image
  have h_card_le : (partition_finite (comp f g)).toFinset.card ≤
      ((f.partition_finite.prod g.partition_finite).image (fun st => st.1 ∩ st.2)).toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Set.Finite.mem_toFinset] at hx ⊢
    exact h_subset hx
  -- The card of an image is at most the card of the domain
  have h_image_card : ((f.partition_finite.prod g.partition_finite).image (fun st => st.1 ∩ st.2)).toFinset.card ≤
      (f.partition_finite.prod g.partition_finite).toFinset.card := by
    classical
    have h_finite_prod : (f.partition ×ˢ g.partition).Finite := f.partition_finite.prod g.partition_finite
    rw [Set.Finite.toFinset_image _ h_finite_prod]
    apply Finset.card_image_le
  -- The card of a product is the product of cards
  have h_prod_card : (f.partition_finite.prod g.partition_finite).toFinset.card =
      f.partition_finite.toFinset.card * g.partition_finite.toFinset.card := by
    classical
    have : (f.partition_finite.prod g.partition_finite).toFinset = f.partition_finite.toFinset ×ˢ g.partition_finite.toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_prod, Finset.mem_product]
    rw [this]
    exact Finset.card_product _ _
  calc (partition_finite (comp f g)).toFinset.card
      ≤ ((f.partition_finite.prod g.partition_finite).image (fun st => st.1 ∩ st.2)).toFinset.card := h_card_le
    _ ≤ (f.partition_finite.prod g.partition_finite).toFinset.card := h_image_card
    _ = f.partition_finite.toFinset.card * g.partition_finite.toFinset.card := h_prod_card

end Composition

section Iteration

/-- The nth iterate of a finite piecewise isometry. -/
def iterate [Nonempty α] (f : FinitePiecewiseIsometry α) : ℕ → FinitePiecewiseIsometry α
  | 0 => FinitePiecewiseIsometry.Constructors.mk_of_finset {Set.univ} (by simp [Finset.Nonempty])
      (by intro s hs; simp [Finset.coe_singleton] at hs; rw [hs]; exact MeasurableSet.univ)
      (by simp [Finset.coe_singleton, Set.sUnion_singleton])
      (by intro s hs t ht hst; simp [Finset.coe_singleton] at hs ht; rw [hs, ht] at hst; contradiction)
      (by intro s hs; simp [Finset.coe_singleton] at hs; rw [hs]; exact Set.univ_nonempty)
      id
      (by intro s hs x _ y _; rfl)
  | n + 1 => f.comp (iterate f n)

/-- Notation for iteration. -/
notation:max f "^[" n "]" => iterate f n

/-- The number of pieces in an iterate grows at most exponentially. -/
theorem card_iterate_le [Nonempty α] (f : FinitePiecewiseIsometry α) (n : ℕ) :
    (iterate f n).card ≤ f.card ^ n := by
  induction n with
  | zero =>
    -- Base case: iterate 0 has 1 piece, f.card ^ 0 = 1
    unfold iterate card
    simp only [pow_zero]
    -- The singleton finset {Set.univ} has cardinality 1
    show (Finset.finite_toSet {Set.univ}).toFinset.card ≤ 1
    simp [Finset.card_singleton]
  | succ n ih =>
    -- Inductive step: use card_comp_le
    calc (iterate f (n + 1)).card
        = (f.comp (iterate f n)).card := rfl
      _ ≤ f.card * (iterate f n).card := card_comp_le f (iterate f n)
      _ ≤ f.card * f.card ^ n := Nat.mul_le_mul_left f.card ih
      _ = f.card ^ (n + 1) := by ring

end Iteration

namespace Complexity

/-- The combinatorial complexity of a finite piecewise isometry, measuring how the partition
refines under iteration. -/
noncomputable def complexity [Nonempty α] (f : FinitePiecewiseIsometry α) (n : ℕ) : ℕ :=
  (f.iterate n).card

/-- Complexity grows at most exponentially in general.

For any finite piecewise isometry, the complexity at step n (number of pieces in the nth iterate)
is bounded by f.card^n. This follows directly from `card_iterate_le`. -/
theorem complexity_exponential_bound [Nonempty α] (f : FinitePiecewiseIsometry α) (n : ℕ) :
    complexity f n ≤ f.card ^ n := by
  unfold complexity
  exact card_iterate_le f n

/-- For interval exchange transformations with bounded refinement, complexity grows linearly.

**Theorem Statement**: If a piecewise isometry has the property that composition refines the
partition by at most an additive constant (rather than multiplicative), then complexity grows
linearly.

**Proof**: Given `∀ m, (f.iterate (m + 1)).card ≤ (f.iterate m).card + C`, we can prove by
induction that `(f.iterate n).card ≤ f.card + n * C`, giving linear growth.

**IET Context**: For interval exchange transformations on d intervals, Rauzy induction shows
that each composition adds at most O(d²) new pieces (rather than multiplying). This bounded
refinement property is the key to linear complexity growth in IETs.

**Note**: This version is provable from the hypothesis. To apply it to actual IETs, one would
need to:
1. Define IETs formally (piecewise isometries on intervals of ℝ)
2. Prove that IETs satisfy the bounded refinement property
3. Instantiate this theorem with that proof

The axiom-free version requires the explicit hypothesis about bounded refinement.

**Edge case**: The bound uses `f.card + n * C`. When `f.card = 0` (empty partition, only possible
for empty α), the base case gives 1 ≤ 0 which is false. To avoid this edge case, we assume
`1 ≤ f.card`, which holds whenever α is nonempty (by `card_pos`). -/
theorem complexity_linear_of_bounded_refinement [Nonempty α] (f : FinitePiecewiseIsometry α)
    (C : ℕ)
    (h_card : 1 ≤ f.card)
    (h_bounded : ∀ m : ℕ, (f.iterate (m + 1)).card ≤ (f.iterate m).card + C) :
    ∀ n : ℕ, complexity f n ≤ f.card + n * C := by
  intro n
  unfold complexity
  -- Prove by induction on n
  induction n with
  | zero =>
    simp only [Nat.zero_mul, add_zero]
    -- f.iterate 0 has cardinality 1, and 1 ≤ f.card by hypothesis
    have h0 : (f.iterate 0).card = 1 := by
      unfold iterate card
      simp only [Constructors.mk_of_finset]
      show (Finset.finite_toSet {Set.univ}).toFinset.card = 1
      rw [Finset.finite_toSet_toFinset]
      exact Finset.card_singleton Set.univ
    rw [h0]
    exact h_card
  | succ n ih =>
    -- Goal: f^[n + 1].card ≤ f.card + (n + 1) * C
    -- By hypothesis: f^[n + 1].card ≤ f^[n].card + C
    -- By IH: f^[n].card ≤ f.card + n * C
    calc (f.iterate (n + 1)).card
        ≤ (f.iterate n).card + C := h_bounded n
      _ ≤ (f.card + n * C) + C := Nat.add_le_add_right ih C
      _ = f.card + (n * C + C) := by ring
      _ = f.card + (n + 1) * C := by ring

end Complexity

namespace Decidability

/-- If partition pieces can be decided, then membership is decidable. -/
noncomputable instance decidable_mem_piece [DecidableEq (Set α)]
    (f : FinitePiecewiseIsometry α) (x : α)
    [∀ s : Set α, Decidable (x ∈ s)] :
    Decidable (∃ s ∈ f.partition, x ∈ s) := by
  -- Convert to decidability over finite set
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
  -- Now use decidability on finsets
  infer_instance

/-- For finite partitions with decidable membership, we can compute which piece a point
belongs to. -/
noncomputable def piece_of (f : FinitePiecewiseIsometry α) (x : α) :
    {s : Set α // s ∈ f.partition ∧ x ∈ s} :=
  -- Use Classical.indefiniteDescription to extract from existence proof
  let ⟨s, hs, hxs⟩ := Classical.indefiniteDescription _ (f.toPiecewiseIsometry.exists_mem_partition x)
  ⟨s, hs, hxs⟩

end Decidability

namespace MeasureTheoretic

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
  -- Use the piece-by-piece preservation from MeasurePreserving.lean
  -- The finite case follows from the general countable case
  exact measurePreserving_of_pieces_preserved f.toPiecewiseIsometry h_meas h_pieces

end MeasureTheoretic

end FinitePiecewiseIsometry

end PiecewiseIsometry
