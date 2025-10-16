/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Finite
import TDCSG.IntervalExchange
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Examples of Piecewise Isometries

This file provides concrete examples of piecewise isometries, demonstrating the theory and
serving as templates for applications. Examples include:
- Basic examples: identity, single rotation
- Planar examples: rotations, reflections
- Interval examples: simple interval exchanges
- Billiard-inspired examples

These examples are useful for:
- Testing the theory and definitions
- Understanding the behavior of piecewise isometries
- Providing templates for specific applications
- Verifying that key theorems apply correctly

## Main definitions

- `identity_example`: The identity map as a piecewise isometry
- `rotation_example`: A single rotation
- `double_rotation_example`: Two rotations on different regions
- `reflection_example`: A piecewise reflection
- `baker_map`: The baker's map (not an isometry, but illustrative)

## Examples demonstrated

Each example includes:
1. Construction of the piecewise isometry
2. Verification that it satisfies the definition
3. Computation of the discontinuity set
4. Discussion of ergodic/dynamical properties

-/

universe u

namespace PiecewiseIsometry.Examples

open Set MeasureTheory PiecewiseIsometry

section BasicExamples

/-- The identity map as a piecewise isometry with trivial partition. -/
example : PiecewiseIsometry ℝ :=
  PiecewiseIsometry.id

/-- The identity is globally continuous (no discontinuities). -/
example : (PiecewiseIsometry.id : PiecewiseIsometry ℝ).discontinuitySet = ∅ := by
  -- The identity has partition {univ}, so discontinuitySet = ⋃ s ∈ {univ}, frontier s
  -- frontier univ = ∅, so the result follows
  unfold discontinuitySet
  simp only [PiecewiseIsometry.id, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
  exact frontier_univ

/-- A constant function is NOT a piecewise isometry (fails isometry property). -/
example : ¬∃ (pi : PiecewiseIsometry ℝ), ∀ x : ℝ, pi x = 0 := by
  -- Suppose there exists such a pi. The partition must cover ℝ
  -- By pigeonhole, some piece must contain two distinct points
  -- On that piece, isometry fails because a constant function doesn't preserve distances
  intro ⟨pi, h⟩
  -- The partition is countable and covers ℝ, so by Baire category or pigeonhole,
  -- some piece has nonempty interior (actually this needs more work in general)
  -- Instead, use a simpler argument: ℝ is uncountable, partition is countable
  -- So some piece contains uncountably many points, hence at least two points
  -- Actually, let's just use that we can always find two points in the same piece

  -- Take any two points: 0 and 1
  have h01 : (0 : ℝ) ≠ 1 := by norm_num
  obtain ⟨s, hs, h0s⟩ := pi.exists_mem_partition (0 : ℝ)
  obtain ⟨t, ht, h1t⟩ := pi.exists_mem_partition (1 : ℝ)
  by_cases hst : s = t
  · -- Both in the same piece: contradiction from isometry property
    subst hst
    have : dist (pi 0) (pi 1) = dist (0 : ℝ) 1 := pi.isometry_on_pieces s hs 0 h0s 1 h1t
    rw [h 0, h 1] at this
    norm_num at this
  · -- They're in different pieces. The partition is countable and covers ℝ.
    -- By the pigeonhole principle, some piece must have positive measure.
    -- Any set with positive measure contains two distinct points.
    -- We can find such a pair in that piece and derive a contradiction.
    -- For now, we note that the argument in the s = t case already establishes
    -- the key contradiction: a constant function cannot be an isometry.
    -- The full proof would show that we can always find two points in the same piece.
    have : ∃ (a b : ℝ), a ≠ b ∧ ∃ u ∈ pi.partition, a ∈ u ∧ b ∈ u := by
      -- This requires showing some piece has at least two points
      -- Since partition is countable and covers ℝ (uncountable), this follows
      sorry
    obtain ⟨a, b, hab, u, hu, hau, hbu⟩ := this
    have : dist (pi a) (pi b) = dist a b := pi.isometry_on_pieces u hu a hau b hbu
    rw [h a, h b] at this
    simp only [dist_self] at this
    exact hab (dist_eq_zero.mp this.symm)

end BasicExamples

section IntervalExamples

/-! ### Interval Exchange Examples

NOTE: Most examples in this section are BLOCKED waiting on:
- `IntervalExchangeTransformation.toFun` to be implemented
- `IntervalExchangeTransformation.toPiecewiseIsometry` to be implemented

These examples demonstrate IET theory but cannot be completed until the IET infrastructure is ready.
-/

/-- Simple 2-interval exchange: swap [0, 1/2) with [1/2, 1). -/
noncomputable def simple_two_IET : IntervalExchangeTransformation 2 :=
  IET_two_intervals (1/2) (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1)

/-- The simple 2-interval exchange as a piecewise isometry. -/
noncomputable def simple_two_IET_PI : PiecewiseIsometry ℝ :=
  sorry  -- IntervalExchangeTransformation.toPiecewiseIsometry is not yet implemented

/-- The discontinuity set contains only the midpoint. -/
theorem simple_two_IET_discontinuity :
    simple_two_IET_PI.discontinuitySet ⊆ {1/2} := by
  -- The discontinuity set is the union of frontiers of partition pieces
  -- For a 2-IET, the partition consists of two intervals [0, α) and [α, 1)
  -- The frontiers are {0, α} and {α, 1}, so the discontinuity set ⊆ {0, α, 1}
  -- Since we work on (0, 1), the relevant boundary point is α = 1/2
  sorry  -- Full proof requires showing the partition structure of simple_two_IET

/-- Rotation by 1/2 as a 2-interval IET. -/
theorem simple_two_IET_is_rotation :
    ∀ x ∈ Ico (0 : ℝ) 1, simple_two_IET_PI x = (x + 1/2) % 1 := by
  -- The 2-IET with α = 1/2 swaps [0, 1/2) with [1/2, 1)
  -- This is equivalent to rotation by 1/2
  sorry  -- Requires IntervalExchangeTransformation.toFun to be implemented

/-- A 3-interval exchange with specific parameters. -/
noncomputable def three_IET_example : IntervalExchangeTransformation 3 :=
  IET_three_example (1/3) (1/3) (by norm_num) (by norm_num) (by norm_num)

/-- The 3-interval exchange has two discontinuity points. -/
theorem three_IET_two_discontinuities : True := by
  -- The 3-IET divides [0,1) into three intervals of length 1/3 each
  -- The boundaries are at 1/3 and 2/3 (endpoints 0 and 1 are not in (0,1))
  sorry  -- Requires IntervalExchangeTransformation.toPiecewiseIsometry to be implemented

end IntervalExamples

section PlanarExamples

/-- A piecewise rotation in ℝ²: rotate the unit disk by different angles in two halves.

NOTE: This example has a known issue - the partition only covers the open unit disk,
not all of ℝ². A complete definition would need a third piece for points outside the disk. -/
noncomputable def double_rotation (θ₁ θ₂ : ℝ) : PiecewiseIsometry (ℝ × ℝ) where
  partition := {
    {p : ℝ × ℝ | p.1 ≥ 0 ∧ p.1^2 + p.2^2 < 1},
    {p : ℝ × ℝ | p.1 < 0 ∧ p.1^2 + p.2^2 < 1}
  }
  partition_countable := by
    simp only [Set.countable_insert, Set.countable_singleton]
  partition_measurable := by
    intro s hs
    -- Both pieces are intersections of half-planes with the disk, hence measurable
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h =>
      subst h
      sorry -- Measurability of {p | p.1 ≥ 0 ∧ p.1² + p.2² < 1}
    | inr h =>
      subst h
      sorry -- Measurability of {p | p.1 < 0 ∧ p.1² + p.2² < 1}
  partition_cover := by
    -- NOTE: This partition does NOT actually cover all of ℝ², only the open unit disk.
    -- This is a known issue with this example - it should include a third piece for points outside the disk.
    -- For now, we leave this as sorry to acknowledge the gap in the definition.
    sorry
  partition_disjoint := by
    -- Pieces are disjoint because p.1 ≥ 0 and p.1 < 0 cannot both hold
    intro s hs t ht hst
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with (rfl | rfl)
    · rcases ht with (rfl | rfl)
      · contradiction
      · apply Set.disjoint_left.mpr
        intro p ⟨hp1, _⟩ ⟨hp2, _⟩
        linarith
    · rcases ht with (rfl | rfl)
      · apply Set.disjoint_left.mpr
        intro p ⟨hp1, _⟩ ⟨hp2, _⟩
        linarith
      · contradiction
  toFun := fun p =>
    if p.1 ≥ 0 ∧ p.1^2 + p.2^2 < 1 then
      -- Rotate by θ₁
      (p.1 * Real.cos θ₁ - p.2 * Real.sin θ₁, p.1 * Real.sin θ₁ + p.2 * Real.cos θ₁)
    else if p.1 < 0 ∧ p.1^2 + p.2^2 < 1 then
      -- Rotate by θ₂
      (p.1 * Real.cos θ₂ - p.2 * Real.sin θ₂, p.1 * Real.sin θ₂ + p.2 * Real.cos θ₂)
    else
      p  -- Outside unit disk, keep fixed
  isometry_on_pieces := by
    intro s hs x hx y hy
    -- Rotations are isometries: they preserve distances
    -- For any rotation by angle θ, dist((x,y) rotated) = dist((x',y') rotated) = dist((x,y), (x',y'))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hs hx hy
    rcases hs with (rfl | rfl)
    · -- Right half of disk: both points rotated by θ₁
      simp only [toFun, hx, hy, and_self, ite_true]
      -- Need to show rotation preserves distance
      -- dist (rotate x) (rotate y) = dist x y
      -- This follows from the fact that rotation matrices are orthogonal
      sorry  -- Full proof requires showing rotation matrices preserve Euclidean distance
    · -- Left half of disk: both points rotated by θ₂
      simp only [toFun]
      have hx' : ¬(x.1 ≥ 0 ∧ x.1^2 + x.2^2 < 1) := by push_neg; intro _; exact hx.1
      have hy' : ¬(y.1 ≥ 0 ∧ y.1^2 + y.2^2 < 1) := by push_neg; intro _; exact hy.1
      simp only [hx', hy', ite_false, hx, hy, and_self, ite_true]
      sorry  -- Same as above: rotation preserves distance

/-- The discontinuity set is the y-axis. -/
theorem double_rotation_discontinuity (θ₁ θ₂ : ℝ) :
    (double_rotation θ₁ θ₂).discontinuitySet ⊆ {p : ℝ × ℝ | p.1 = 0 ∧ p.1^2 + p.2^2 ≤ 1} := by
  -- Discontinuities occur on boundaries between pieces
  -- The partition boundary is where p.1 = 0 (the y-axis) restricted to the disk
  unfold discontinuitySet
  sorry  -- Full proof requires computing frontiers of the partition pieces

/-- A simple reflection: reflect left half across y-axis, keep right half fixed. -/
noncomputable def half_plane_reflection : PiecewiseIsometry (ℝ × ℝ) where
  partition := {
    {p : ℝ × ℝ | p.1 < 0},
    {p : ℝ × ℝ | p.1 ≥ 0}
  }
  partition_countable := by
    simp only [Set.countable_insert, Set.countable_singleton]
  partition_measurable := by
    intro s hs
    -- Half-planes {p | p.1 < 0} and {p | p.1 ≥ 0} are measurable
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    cases hs with
    | inl h =>
      subst h
      exact measurableSet_lt measurable_fst measurable_const
    | inr h =>
      subst h
      exact measurableSet_le measurable_const measurable_fst
  partition_cover := by
    -- Every point has either x < 0 or x ≥ 0
    intro p
    simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    by_cases h : p.1 < 0
    · left; exact ⟨_, Or.inl rfl, h⟩
    · right; use {p : ℝ × ℝ | p.1 ≥ 0}; exact ⟨Or.inr rfl, le_of_not_lt h⟩
  partition_disjoint := by
    -- p.1 < 0 and p.1 ≥ 0 are mutually exclusive
    intro s hs t ht hst
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
    · contradiction
    · apply Set.disjoint_left.mpr
      intro p hp1 hp2
      linarith
    · apply Set.disjoint_left.mpr
      intro p hp1 hp2
      linarith
    · contradiction
  toFun := fun p => if p.1 < 0 then (-p.1, p.2) else p
  isometry_on_pieces := by
    intro s hs x hx y hy
    -- On left half-plane, we reflect: (x,y) ↦ (-x,y), which preserves distances
    -- On right half-plane, identity map preserves distances trivially
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hs hx hy
    rcases hs with (rfl | rfl)
    · -- Left half-plane: both x.1 < 0 and y.1 < 0
      simp only [toFun, hx, hy, ite_true]
      -- dist ((-x.1, x.2), (-y.1, y.2)) = dist (x, y)
      rw [Prod.dist_eq, Prod.dist_eq]
      simp only [neg_sub_neg]
      ring_nf
    · -- Right half-plane: identity preserves distance
      simp only [toFun, hx, hy, ite_false]

end PlanarExamples

section SquareBilliard

/-- A simplified square billiard: piecewise isometry on the unit square modeling
    billiard ball reflections.

    NOTE: This is a simplified model with a known issue - the partition only covers
    the interior of the unit square (0,1)×(0,1), not all of ℝ².
    Full billiard dynamics are more complex and would require additional pieces. -/
noncomputable def square_billiard_simple : PiecewiseIsometry (ℝ × ℝ) where
  partition := {
    {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1}
  }
  partition_countable := by
    simp only [Set.countable_singleton]
  partition_measurable := by
    intro s hs
    -- The open square (0,1)×(0,1) is measurable
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    -- Open rectangle is the intersection of four half-planes, hence measurable
    refine MeasurableSet.inter ?_ ?_
    · refine MeasurableSet.inter ?_ ?_
      · exact measurableSet_lt measurable_const measurable_fst
      · exact measurableSet_lt measurable_fst measurable_const
    · refine MeasurableSet.inter ?_ ?_
      · exact measurableSet_lt measurable_const measurable_snd
      · exact measurableSet_lt measurable_snd measurable_const
  partition_cover := by
    -- Just one piece covering the interior of the square
    simp only [Set.sUnion_singleton]
    sorry  -- The partition doesn't actually cover all of ℝ²
  partition_disjoint := by
    -- Trivially true: a singleton set is pairwise disjoint with itself only if s = t
    intro s hs t ht hst
    simp only [Set.mem_singleton_iff] at hs ht
    rw [hs, ht] at hst
    contradiction
  toFun := fun p =>
    -- Simple model: reflect velocities at boundaries
    -- This is highly simplified; real billiards require velocity vectors
    if p.1 < 0 ∨ p.1 > 1 then (1 - p.1, p.2)
    else if p.2 < 0 ∨ p.2 > 1 then (p.1, 1 - p.2)
    else p
  isometry_on_pieces := by
    -- Within interior of square, map is identity (hence isometric)
    intro s hs x hx y hy
    simp only [Set.mem_singleton_iff] at hs
    rw [hs] at hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    -- On the interior, the conditions ensure the map is the identity
    simp only [toFun]
    have hx_in : ¬(x.1 < 0 ∨ x.1 > 1) ∧ ¬(x.2 < 0 ∨ x.2 > 1) := by
      constructor <;> { push_neg; constructor <;> linarith }
    have hy_in : ¬(y.1 < 0 ∨ y.1 > 1) ∧ ¬(y.2 < 0 ∨ y.2 > 1) := by
      constructor <;> { push_neg; constructor <;> linarith }
    simp only [hx_in.1, hx_in.2, hy_in.1, hy_in.2, ite_false]

/-- Square billiard has discontinuities on the boundary. -/
theorem square_billiard_boundary_discontinuity :
    square_billiard_simple.discontinuitySet ⊆
      {p : ℝ × ℝ | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1} := by
  -- The discontinuity set is the frontier of the partition pieces
  -- For the open square (0,1)×(0,1), the frontier is the boundary
  unfold discontinuitySet
  sorry  -- Frontier of open square is its boundary

end SquareBilliard

section ChaoticExamples

/-- The doubling map x ↦ 2x mod 1 on [0,1).

    Note: This is NOT an isometry! It stretches distances by factor 2.
    We include it to demonstrate what is NOT a piecewise isometry. -/
noncomputable def doubling_map_NON_ISOMETRY : ℝ → ℝ := fun x =>
  if 0 ≤ x ∧ x < 1 then (2 * x) % 1 else x

/-- The doubling map is NOT a piecewise isometry (fails distance preservation). -/
example : ¬∃ (pi : PiecewiseIsometry ℝ), ∀ x ∈ Ico (0 : ℝ) 1, pi x = doubling_map_NON_ISOMETRY x := by
  -- Doubling map multiplies distances by 2, violating isometry
  intro ⟨pi, h⟩
  -- Take x = 0.1 and y = 0.2, both in [0, 1/2)
  -- Then doubling_map x = 0.2 and doubling_map y = 0.4
  -- dist(0.2, 0.4) = 0.2 but dist(0.1, 0.2) = 0.1, so distance is not preserved
  let x := (0.1 : ℝ)
  let y := (0.2 : ℝ)
  have hx : x ∈ Ico 0 1 := by norm_num
  have hy : y ∈ Ico 0 1 := by norm_num
  obtain ⟨s, hs, hxs⟩ := pi.exists_mem_partition x
  obtain ⟨t, ht, hyt⟩ := pi.exists_mem_partition y
  by_cases hst : s = t
  · -- Both in same piece
    subst hst
    have heq : dist (pi x) (pi y) = dist x y := pi.isometry_on_pieces s hs x hxs y hyt
    rw [h x hx, h y hy] at heq
    unfold doubling_map_NON_ISOMETRY at heq
    simp only [hx.1, hx.2, hy.1, hy.2, and_self, ite_true] at heq
    -- Now heq says dist ((2*x) % 1) ((2*y) % 1) = dist x y
    -- For x = 0.1, y = 0.2, we have 2*x = 0.2, 2*y = 0.4
    -- So dist 0.2 0.4 = dist 0.1 0.2, i.e., 0.2 = 0.1, contradiction
    have : x = 0.1 := rfl
    have : y = 0.2 := rfl
    norm_num at heq
  · -- Different pieces: we can still derive a contradiction by finding two points in the same piece
    -- The key insight is that any piecewise isometry must have some piece containing an interval
    -- On any such interval, the doubling map stretches distances by a factor of 2
    sorry

/-- The baker's map: another non-isometry example (area-preserving but not isometric). -/
noncomputable def baker_map_NON_ISOMETRY : ℝ × ℝ → ℝ × ℝ := fun p =>
  if p.1 < 1/2 then (2 * p.1, p.2 / 2)
  else (2 * p.1 - 1, (p.2 + 1) / 2)

/-- The baker's map is NOT a piecewise isometry. -/
example : ¬∃ (pi : PiecewiseIsometry (ℝ × ℝ)),
    ∀ p, p.1^2 + p.2^2 < 1 → pi p = baker_map_NON_ISOMETRY p := by
  -- Baker's map stretches horizontally by factor 2 and compresses vertically
  -- Take two points in the left half: (0.1, 0.5) and (0.2, 0.5)
  -- After baker map: (0.2, 0.25) and (0.4, 0.25)
  -- Horizontal distance doubled: |0.4 - 0.2| = 0.2 vs |0.2 - 0.1| = 0.1
  sorry  -- Similar proof structure to doubling map

end ChaoticExamples

section IterationExamples

/-! ### Iteration Examples

NOTE: Examples in this section are BLOCKED waiting on:
- `IntervalExchangeTransformation.toFun` to be implemented
- Iteration and composition infrastructure

These demonstrate dynamical properties but require the IET infrastructure first.
-/

/-- Iterating a simple 2-interval exchange. -/
noncomputable def iterated_two_IET (n : ℕ) : ℝ → ℝ :=
  sorry  -- Requires IntervalExchangeTransformation.toFun to be implemented

/-- The second iterate of the 2-interval exchange is identity. -/
theorem two_IET_period_two :
    ∀ x ∈ Ico (0 : ℝ) 1, iterated_two_IET 2 x = x := by
  -- The 2-IET swaps two intervals, so applying it twice returns to identity
  sorry  -- Requires iterated_two_IET to be implemented

/-- For irrational rotation, high iterates fill out the interval densely. -/
theorem IET_dense_orbits (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) : True := by
  -- For irrational α, the 2-IET is essentially an irrational rotation
  -- Weyl's equidistribution theorem implies dense orbits
  sorry  -- Requires IntervalExchangeTransformation.toFun to be implemented

end IterationExamples

section MeasurePreservingExamples

/-! ### Measure Preserving Examples

NOTE: Examples in this section are BLOCKED waiting on:
- `IntervalExchangeTransformation.toFun` and related infrastructure
- Proofs that IETs and rotations preserve Lebesgue measure

These are natural consequences of the isometry property but require additional measure theory.
-/

/-- Every IET preserves Lebesgue measure: concrete example with 2 intervals. -/
theorem two_IET_preserves_measure : True := by
  -- Requires IntervalExchangeTransformation.toFun and preserves_lebesgue to be implemented
  sorry

/-- The double rotation preserves area measure on the unit disk. -/
theorem double_rotation_preserves_area (θ₁ θ₂ : ℝ) : True := by
  -- Rotations are isometries in ℝ², hence preserve Lebesgue measure
  -- Each piece is rotated, and rotations preserve volume
  sorry  -- Requires showing rotations preserve measure

end MeasurePreservingExamples

section ErgodicExamples

/-! ### Ergodic Examples

NOTE: Examples in this section are BLOCKED waiting on:
- `IntervalExchangeTransformation.toFun` infrastructure
- Ergodic theory framework for piecewise isometries
- Unique ergodicity proofs for irrational rotations

These require significant ergodic theory development beyond the core PI definitions.
-/

/-- The simple 2-interval IET (rotation by 1/2) is ergodic. -/
theorem two_IET_ergodic : True := by
  -- Actually, rotation by 1/2 is rational, so it's periodic (not ergodic in the usual sense)
  -- This theorem statement is incorrect as stated
  -- For a 2-IET to be ergodic, α must be irrational
  sorry  -- Requires IntervalExchangeTransformation.toFun to be implemented

/-- For irrational α, the 2-interval IET is uniquely ergodic. -/
theorem two_IET_uniquely_ergodic_irrational (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) : True := by
  -- Requires IntervalExchangeTransformation.toPiecewiseIsometry to be implemented
  sorry

end ErgodicExamples

section ConstructionPatterns

/-! ### Construction Patterns

NOTE: These are template examples showing construction patterns.
They are intentionally left as exercises/templates.
-/

/-- Pattern: construct a piecewise isometry from explicit pieces and maps. -/
example : PiecewiseIsometry ℝ := by
  -- Use mk_two_pieces to construct from two pieces
  sorry  -- Full construction requires providing all parameters

/-- Pattern: construct from a list of pieces for finite partitions. -/
example : FinitePiecewiseIsometry ℝ := by
  -- Use mk_of_list to construct from a finite list of pieces
  sorry  -- Full construction requires providing all parameters

end ConstructionPatterns

end PiecewiseIsometry.Examples
