/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.TwoDisk

/-!
# Two-Disk Compound Symmetry Groups

This file contains theorems about the two-disk compound symmetry group construction.

## Main definitions (imported from TDCSG.Definitions.TwoDisk)

- `TwoDiskSystem`: Two disks with specified radii and rotation orders
- `TwoDiskSystem.diskL`: The left disk in the system
- `TwoDiskSystem.diskR`: The right disk in the system
- `TwoDiskSystem.rotationA`: Rotation A (on left disk)
- `TwoDiskSystem.rotationB`: Rotation B (on right disk)
- `TwoDiskSystem.basicPartition`: The initial partition
- `TwoDiskSystem.toPiecewiseIsometry_a`: Generator A as piecewise isometry
- `TwoDiskSystem.toPiecewiseIsometry_b`: Generator B as piecewise isometry

## References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)

-/

open scoped RealInnerProductSpace
open Planar
open Classical
open TDCSG.Definitions

namespace CompoundSymmetry

namespace TwoDiskSystem

variable (sys : TwoDiskSystem)

/-- The basic partition is countable (it's finite) -/
theorem basicPartition_countable : (basicPartition sys).Countable := by
  unfold basicPartition
  have : ({diskL sys, diskR sys, exterior sys} : Set (Set ℝ²)).Finite := by
    rw [Set.finite_insert, Set.finite_insert]
    exact Set.finite_singleton _
  exact this.countable

/-- Distance between two points on the x-axis in ℝ² -/
lemma dist_on_x_axis (a b : ℝ) :
    let p : ℝ² := fun i => if i = 0 then a else 0
    let q : ℝ² := fun i => if i = 0 then b else 0
    dist p q = |a - b| := by
  intro p q
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two]
  -- Simplify the function applications
  simp only [p, q]
  -- Now we have sqrt of sum of squared norms
  simp only [Fin.isValue, Real.norm_eq_abs]
  norm_num
  exact Real.sqrt_sq_eq_abs (a - b)


/-- The basic partition is measurable -/
theorem basicPartition_measurable : ∀ s ∈ basicPartition sys, MeasurableSet s := by
  intro s hs
  unfold basicPartition at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl | rfl)
  · -- leftDisk case
    unfold diskL Disk
    exact Metric.isClosed_closedBall.measurableSet
  · -- rightDisk case
    unfold diskR Disk
    exact Metric.isClosed_closedBall.measurableSet
  · -- exterior case
    unfold exterior
    apply MeasurableSet.compl
    apply MeasurableSet.union
    · unfold diskL Disk
      exact Metric.isClosed_closedBall.measurableSet
    · unfold diskR Disk
      exact Metric.isClosed_closedBall.measurableSet

/-- The basic partition covers the entire plane -/
theorem basicPartition_cover : ⋃₀ basicPartition sys = Set.univ := by
  unfold basicPartition
  ext x
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h1 : x ∈ diskL sys
  · exact ⟨diskL sys, Or.inl rfl, h1⟩
  · by_cases h2 : x ∈ diskR sys
    · exact ⟨diskR sys, Or.inr (Or.inl rfl), h2⟩
    · -- x is in exterior
      refine ⟨exterior sys, Or.inr (Or.inr rfl), ?_⟩
      unfold exterior
      simp only [Set.mem_compl_iff, Set.mem_union]
      push_neg
      exact ⟨h1, h2⟩


/-- Each partition piece is nonempty -/
theorem basicPartition_nonempty : ∀ s ∈ basicPartition sys, s.Nonempty := by
  intro s hs
  unfold basicPartition at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl | rfl)
  · -- leftDisk is nonempty (contains its center)
    unfold diskL Disk
    use leftCenter
    simp only [Metric.mem_closedBall, dist_self, le_of_lt sys.r1_pos]
  · -- rightDisk is nonempty (contains its center)
    unfold diskR Disk
    use rightCenter
    simp only [Metric.mem_closedBall, dist_self, le_of_lt sys.r2_pos]
  · -- exterior is nonempty (contains a far away point)
    unfold exterior
    -- Use a point on the x-axis far to the left: (-1 - 10*r1 - 10*r2, 0)
    -- This is clearly outside both disks (centers at -1 and 1)
    let x_coord := -1 - 10 * sys.r1 - 10 * sys.r2
    let p : ℝ² := fun i => if i = 0 then x_coord else 0
    use p
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · -- Not in leftDisk
      unfold diskL Disk leftCenter
      simp only [Metric.mem_closedBall, not_le]
      -- leftCenter = (-1, 0), p = (-1 - 10r1 - 10r2, 0)
      -- dist = |x_coord - (-1)| = |-10r1 - 10r2| = 10r1 + 10r2 > r1
      have : sys.r1 < dist p (fun i => if i = 0 then -1 else 0) := by
        rw [dist_on_x_axis]
        simp only [x_coord]
        ring_nf
        rw [abs_of_neg]
        · linarith [sys.r1_pos, sys.r2_pos]
        · linarith [sys.r1_pos, sys.r2_pos]
      exact this
    · -- Not in rightDisk
      unfold diskR Disk rightCenter
      simp only [Metric.mem_closedBall, not_le]
      -- rightCenter = (1, 0), p = (-1 - 10r1 - 10r2, 0)
      -- dist = |x_coord - 1| = |-2 - 10r1 - 10r2| = 2 + 10r1 + 10r2 > r2
      have : sys.r2 < dist p (fun i => if i = 0 then 1 else 0) := by
        rw [dist_on_x_axis]
        simp only [x_coord]
        ring_nf
        rw [abs_of_neg]
        · linarith [sys.r1_pos, sys.r2_pos]
        · linarith [sys.r1_pos, sys.r2_pos]
      exact this

/-! ### Partition A theorems (for generator A) -/

/-- Partition A is countable (it's finite) -/
theorem partitionA_countable : (partitionA sys).Countable := by
  unfold partitionA
  have : ({diskL sys, (diskL sys)ᶜ} : Set (Set ℝ²)).Finite := by
    rw [Set.finite_insert]
    exact Set.finite_singleton _
  exact this.countable

/-- Partition A is measurable -/
theorem partitionA_measurable : ∀ s ∈ partitionA sys, MeasurableSet s := by
  intro s hs
  unfold partitionA at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · unfold diskL Disk
    exact Metric.isClosed_closedBall.measurableSet
  · exact (Metric.isClosed_closedBall.measurableSet).compl

/-- Partition A covers the entire plane -/
theorem partitionA_cover : ⋃₀ partitionA sys = Set.univ := by
  unfold partitionA
  ext x
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x ∈ diskL sys
  · exact ⟨diskL sys, Or.inl rfl, h⟩
  · exact ⟨(diskL sys)ᶜ, Or.inr rfl, h⟩

/-- Partition A pieces are pairwise disjoint -/
theorem partitionA_disjoint : (partitionA sys).PairwiseDisjoint id := by
  intro s hs t ht hst
  unfold partitionA at hs ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
  · contradiction
  · exact disjoint_compl_right
  · exact disjoint_compl_left
  · contradiction

/-- Each partition A piece is nonempty -/
theorem partitionA_nonempty : ∀ s ∈ partitionA sys, s.Nonempty := by
  intro s hs
  unfold partitionA at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · -- leftDisk is nonempty (contains its center)
    unfold diskL Disk
    use leftCenter
    simp only [Metric.mem_closedBall, dist_self]
    exact le_of_lt sys.r1_pos
  · -- complement is nonempty (contains a far right point)
    use (fun i : Fin 2 => if i = 0 then 10 * sys.r1 else 0)
    simp only [Set.mem_compl_iff]
    unfold diskL Disk leftCenter
    simp only [Metric.mem_closedBall, not_le]
    rw [dist_on_x_axis]
    ring_nf
    rw [abs_of_pos]
    · linarith [sys.r1_pos]
    · linarith [sys.r1_pos]

/-! ### Partition B theorems (for generator B) -/

/-- Partition B is countable (it's finite) -/
theorem partitionB_countable : (partitionB sys).Countable := by
  unfold partitionB
  have : ({diskR sys, (diskR sys)ᶜ} : Set (Set ℝ²)).Finite := by
    rw [Set.finite_insert]
    exact Set.finite_singleton _
  exact this.countable

/-- Partition B is measurable -/
theorem partitionB_measurable : ∀ s ∈ partitionB sys, MeasurableSet s := by
  intro s hs
  unfold partitionB at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · unfold diskR Disk
    exact Metric.isClosed_closedBall.measurableSet
  · exact (Metric.isClosed_closedBall.measurableSet).compl

/-- Partition B covers the entire plane -/
theorem partitionB_cover : ⋃₀ partitionB sys = Set.univ := by
  unfold partitionB
  ext x
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x ∈ diskR sys
  · exact ⟨diskR sys, Or.inl rfl, h⟩
  · exact ⟨(diskR sys)ᶜ, Or.inr rfl, h⟩

/-- Partition B pieces are pairwise disjoint -/
theorem partitionB_disjoint : (partitionB sys).PairwiseDisjoint id := by
  intro s hs t ht hst
  unfold partitionB at hs ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with (rfl | rfl) <;> rcases ht with (rfl | rfl)
  · contradiction
  · exact disjoint_compl_right
  · exact disjoint_compl_left
  · contradiction

/-- Each partition B piece is nonempty -/
theorem partitionB_nonempty : ∀ s ∈ partitionB sys, s.Nonempty := by
  intro s hs
  unfold partitionB at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · -- rightDisk is nonempty (contains its center)
    unfold diskR Disk
    use rightCenter
    simp only [Metric.mem_closedBall, dist_self]
    exact le_of_lt sys.r2_pos
  · -- complement is nonempty (contains a far left point)
    use (fun i : Fin 2 => if i = 0 then -10 * sys.r2 else 0)
    simp only [Set.mem_compl_iff]
    unfold diskR Disk rightCenter
    simp only [Metric.mem_closedBall, not_le]
    rw [dist_on_x_axis]
    ring_nf
    rw [abs_of_neg]
    · linarith [sys.r2_pos]
    · linarith [sys.r2_pos]

/-- Rotation A preserves distances on the left disk -/
theorem rotationA_isometry_on_diskL : ∀ x ∈ diskL sys, ∀ y ∈ diskL sys,
    dist (rotationA sys x) (rotationA sys y) = dist x y := by
  intro x hx y hy
  unfold rotationA
  -- Both x and y are in leftDisk, so the if conditions are true
  simp only [hx, hy, ite_true]
  -- rotateAround preserves distances
  exact Planar.rotateAround_dist leftCenter (angleA sys) x y

/-- Rotation B preserves distances on the right disk -/
theorem rotationB_isometry_on_diskR : ∀ x ∈ diskR sys, ∀ y ∈ diskR sys,
    dist (rotationB sys x) (rotationB sys y) = dist x y := by
  intro x hx y hy
  unfold rotationB
  -- Both x and y are in rightDisk, so the if conditions are true
  simp only [hx, hy, ite_true]
  -- rotateAround preserves distances
  exact Planar.rotateAround_dist rightCenter (angleB sys) x y

/-- Rotation A is the identity on the complement of the left disk -/
theorem rotationA_eq_id_on_compl : ∀ x ∉ diskL sys, rotationA sys x = x := by
  intro x hx
  unfold rotationA
  simp [hx]

/-- Rotation B is the identity on the complement of the right disk -/
theorem rotationB_eq_id_on_compl : ∀ x ∉ diskR sys, rotationB sys x = x := by
  intro x hx
  unfold rotationB
  simp [hx]

/-- The isometry_on_pieces proof for generator A -/
theorem toPiecewiseIsometry_a_isometry_on_pieces :
    ∀ s ∈ partitionA sys, ∀ x ∈ s, ∀ y ∈ s,
      dist (rotationA sys x) (rotationA sys y) = dist x y := by
  intro s hs x hx y hy
  unfold partitionA at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · -- s = leftDisk: rotationA is isometric on leftDisk
    exact rotationA_isometry_on_diskL sys x hx y hy
  · -- s = leftDisk^c: rotationA is identity on leftDisk^c
    simp only [Set.mem_compl_iff] at hx hy
    rw [rotationA_eq_id_on_compl sys x hx, rotationA_eq_id_on_compl sys y hy]

/-- The isometry_on_pieces proof for generator B -/
theorem toPiecewiseIsometry_b_isometry_on_pieces :
    ∀ s ∈ partitionB sys, ∀ x ∈ s, ∀ y ∈ s,
      dist (rotationB sys x) (rotationB sys y) = dist x y := by
  intro s hs x hx y hy
  unfold partitionB at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · -- s = rightDisk: rotationB is isometric on rightDisk
    exact rotationB_isometry_on_diskR sys x hx y hy
  · -- s = rightDisk^c: rotationB is identity on rightDisk^c
    simp only [Set.mem_compl_iff] at hx hy
    rw [rotationB_eq_id_on_compl sys x hx, rotationB_eq_id_on_compl sys y hy]

end TwoDiskSystem

/-- Notation for single-disk compound symmetry group -/
scoped notation "GG_" n "(" r ")" => TwoDiskSystem.mk r r n n

/-- Notation for two-disk compound symmetry group with different parameters -/
scoped notation "GG_{" n1 "," n2 "}(" r1 "," r2 ")" => TwoDiskSystem.mk r1 r2 n1 n2

/-- Example: The basic two-disk system with equal radii and 3-fold rotations -/
example : TwoDiskSystem := {
  r1 := 1
  r2 := 1
  n1 := 3
  n2 := 3
  r1_pos := by norm_num
  r2_pos := by norm_num
  n1_ge := by norm_num
  n2_ge := by norm_num
}

/-- Example: Asymmetric two-disk system -/
example : TwoDiskSystem := {
  r1 := 1
  r2 := 2
  n1 := 3
  n2 := 5
  r1_pos := by norm_num
  r2_pos := by norm_num
  n1_ge := by norm_num
  n2_ge := by norm_num
}

end CompoundSymmetry
