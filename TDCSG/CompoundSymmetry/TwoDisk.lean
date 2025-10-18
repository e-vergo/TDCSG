/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Planar.Rotations
import TDCSG.Planar.Disks

/-!
# Two-Disk Compound Symmetry Groups

This file formalizes the two-disk compound symmetry group construction.

## Main definitions

- `TwoDiskSystem`: Two disks with specified radii and rotation orders
- `TwoDiskSystem.leftDisk`: The left disk in the system
- `TwoDiskSystem.rightDisk`: The right disk in the system
- `TwoDiskSystem.genA`: Generator A (rotation on left disk)
- `TwoDiskSystem.genB`: Generator B (rotation on right disk)
- `TwoDiskSystem.basicPartition`: The initial partition
- `TwoDiskSystem.toPiecewiseIsometry_a`: Generator A as piecewise isometry
- `TwoDiskSystem.toPiecewiseIsometry_b`: Generator B as piecewise isometry

## References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)

-/

open scoped RealInnerProductSpace
open Planar
open Classical

namespace CompoundSymmetry

/-- A two-disk system with specified radii and rotation orders. -/
structure TwoDiskSystem where
  /-- Radius of the left disk -/
  r1 : ℝ
  /-- Radius of the right disk -/
  r2 : ℝ
  /-- Rotation order for the left disk -/
  n1 : ℕ
  /-- Rotation order for the right disk -/
  n2 : ℕ
  /-- The left disk has positive radius -/
  r1_pos : 0 < r1
  /-- The right disk has positive radius -/
  r2_pos : 0 < r2
  /-- The left disk has at least 2-fold rotation symmetry -/
  n1_ge : 2 ≤ n1
  /-- The right disk has at least 2-fold rotation symmetry -/
  n2_ge : 2 ≤ n2

namespace TwoDiskSystem

variable (sys : TwoDiskSystem)

/-- The center of the left disk (positioned at (-r1, 0)) -/
noncomputable def leftCenter : ℝ² :=
  fun i => if i = 0 then -sys.r1 else 0

/-- The center of the right disk (positioned at (r2, 0)) -/
noncomputable def rightCenter : ℝ² :=
  fun i => if i = 0 then sys.r2 else 0

/-- The left disk -/
noncomputable def leftDisk : Set ℝ² :=
  TDCSG.Disk (leftCenter sys) sys.r1

/-- The right disk -/
noncomputable def rightDisk : Set ℝ² :=
  TDCSG.Disk (rightCenter sys) sys.r2

/-- The exterior region (outside both disks) -/
noncomputable def exterior : Set ℝ² :=
  (leftDisk sys ∪ rightDisk sys)ᶜ

/-- The rotation angle for the left disk generator -/
noncomputable def angleA : Real.Angle :=
  (2 * Real.pi / sys.n1 : ℝ)

/-- The rotation angle for the right disk generator -/
noncomputable def angleB : Real.Angle :=
  (2 * Real.pi / sys.n2 : ℝ)

/-- Generator A: rotation by 2π/n1 around the center of the left disk -/
noncomputable def genA : ℝ² → ℝ² :=
  fun x => if x ∈ leftDisk sys then
    rotateAround (leftCenter sys) (angleA sys) x
  else
    x

/-- Generator B: rotation by 2π/n2 around the center of the right disk -/
noncomputable def genB : ℝ² → ℝ² :=
  fun x => if x ∈ rightDisk sys then
    rotateAround (rightCenter sys) (angleB sys) x
  else
    x

/-- The partition for generator A. -/
noncomputable def partitionA : Set (Set ℝ²) :=
  {leftDisk sys, (leftDisk sys)ᶜ}

/-- The partition for generator B. -/
noncomputable def partitionB : Set (Set ℝ²) :=
  {rightDisk sys, (rightDisk sys)ᶜ}

/-- The basic partition for the two-disk system. -/
noncomputable def basicPartition : Set (Set ℝ²) :=
  {leftDisk sys, rightDisk sys, exterior sys}

/-- The basic partition is countable (it's finite) -/
theorem basicPartition_countable : (basicPartition sys).Countable := by
  unfold basicPartition
  have : ({leftDisk sys, rightDisk sys, exterior sys} : Set (Set ℝ²)).Finite := by
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
  simp only [Pi.sub_apply, Fin.sum_univ_two]
  -- Simplify the function applications
  simp only [p, q, Pi.sub_apply]
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
    unfold leftDisk TDCSG.Disk
    exact Metric.isClosed_closedBall.measurableSet
  · -- rightDisk case
    unfold rightDisk TDCSG.Disk
    exact Metric.isClosed_closedBall.measurableSet
  · -- exterior case
    unfold exterior
    apply MeasurableSet.compl
    apply MeasurableSet.union
    · unfold leftDisk TDCSG.Disk
      exact Metric.isClosed_closedBall.measurableSet
    · unfold rightDisk TDCSG.Disk
      exact Metric.isClosed_closedBall.measurableSet

/-- The basic partition covers the entire plane -/
theorem basicPartition_cover : ⋃₀ basicPartition sys = Set.univ := by
  unfold basicPartition
  ext x
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h1 : x ∈ leftDisk sys
  · exact ⟨leftDisk sys, Or.inl rfl, h1⟩
  · by_cases h2 : x ∈ rightDisk sys
    · exact ⟨rightDisk sys, Or.inr (Or.inl rfl), h2⟩
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
    unfold leftDisk TDCSG.Disk
    use leftCenter sys
    simp only [Metric.mem_closedBall, dist_self, le_of_lt sys.r1_pos]
  · -- rightDisk is nonempty (contains its center)
    unfold rightDisk TDCSG.Disk
    use rightCenter sys
    simp only [Metric.mem_closedBall, dist_self, le_of_lt sys.r2_pos]
  · -- exterior is nonempty (contains a far away point)
    unfold exterior
    -- Use a point on the x-axis far to the left: (-10*r1 - r2, 0)
    -- This is clearly outside both disks
    let x_coord := -(10 * sys.r1 + sys.r2)
    let p : ℝ² := fun i => if i = 0 then x_coord else 0
    use p
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · -- Not in leftDisk
      unfold leftDisk TDCSG.Disk leftCenter
      simp only [Metric.mem_closedBall, not_le]
      -- leftCenter = (-r1, 0), p = (-10r1 - r2, 0)
      -- dist = |-10r1 - r2 - (-r1)| = |-9r1 - r2| = 9r1 + r2 > r1
      have : sys.r1 < dist p (fun i => if i = 0 then -sys.r1 else 0) := by
        rw [dist_on_x_axis]
        simp only [x_coord]
        ring_nf
        rw [abs_of_neg]
        · linarith [sys.r1_pos, sys.r2_pos]
        · linarith [sys.r1_pos, sys.r2_pos]
      exact this
    · -- Not in rightDisk
      unfold rightDisk TDCSG.Disk rightCenter
      simp only [Metric.mem_closedBall, not_le]
      -- rightCenter = (r2, 0), p = (-10r1 - r2, 0)
      -- dist = |r2 - (-10r1 - r2)| = |10r1 + 2r2| = 10r1 + 2r2 > r2
      have : sys.r2 < dist p (fun i => if i = 0 then sys.r2 else 0) := by
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
  have : ({leftDisk sys, (leftDisk sys)ᶜ} : Set (Set ℝ²)).Finite := by
    rw [Set.finite_insert]
    exact Set.finite_singleton _
  exact this.countable

/-- Partition A is measurable -/
theorem partitionA_measurable : ∀ s ∈ partitionA sys, MeasurableSet s := by
  intro s hs
  unfold partitionA at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · unfold leftDisk TDCSG.Disk
    exact Metric.isClosed_closedBall.measurableSet
  · exact (Metric.isClosed_closedBall.measurableSet).compl

/-- Partition A covers the entire plane -/
theorem partitionA_cover : ⋃₀ partitionA sys = Set.univ := by
  unfold partitionA
  ext x
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x ∈ leftDisk sys
  · exact ⟨leftDisk sys, Or.inl rfl, h⟩
  · exact ⟨(leftDisk sys)ᶜ, Or.inr rfl, h⟩

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
    unfold leftDisk TDCSG.Disk
    use leftCenter sys
    simp only [Metric.mem_closedBall, dist_self, le_of_lt sys.r1_pos]
  · -- complement is nonempty (contains a far right point)
    use (fun i : Fin 2 => if i = 0 then 10 * sys.r1 else 0)
    simp only [Set.mem_compl_iff]
    unfold leftDisk TDCSG.Disk leftCenter
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
  have : ({rightDisk sys, (rightDisk sys)ᶜ} : Set (Set ℝ²)).Finite := by
    rw [Set.finite_insert]
    exact Set.finite_singleton _
  exact this.countable

/-- Partition B is measurable -/
theorem partitionB_measurable : ∀ s ∈ partitionB sys, MeasurableSet s := by
  intro s hs
  unfold partitionB at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl)
  · unfold rightDisk TDCSG.Disk
    exact Metric.isClosed_closedBall.measurableSet
  · exact (Metric.isClosed_closedBall.measurableSet).compl

/-- Partition B covers the entire plane -/
theorem partitionB_cover : ⋃₀ partitionB sys = Set.univ := by
  unfold partitionB
  ext x
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x ∈ rightDisk sys
  · exact ⟨rightDisk sys, Or.inl rfl, h⟩
  · exact ⟨(rightDisk sys)ᶜ, Or.inr rfl, h⟩

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
    unfold rightDisk TDCSG.Disk
    use rightCenter sys
    simp only [Metric.mem_closedBall, dist_self, le_of_lt sys.r2_pos]
  · -- complement is nonempty (contains a far left point)
    use (fun i : Fin 2 => if i = 0 then -10 * sys.r2 else 0)
    simp only [Set.mem_compl_iff]
    unfold rightDisk TDCSG.Disk rightCenter
    simp only [Metric.mem_closedBall, not_le]
    rw [dist_on_x_axis]
    ring_nf
    rw [abs_of_neg]
    · linarith [sys.r2_pos]
    · linarith [sys.r2_pos]

/-- Generator A preserves distances on the left disk -/
theorem genA_isometry_on_leftDisk : ∀ x ∈ leftDisk sys, ∀ y ∈ leftDisk sys,
    dist (sys.genA x) (sys.genA y) = dist x y := by
  intro x hx y hy
  unfold genA
  -- Both x and y are in leftDisk, so the if conditions are true
  simp only [hx, hy, ite_true]
  -- rotateAround preserves distances
  exact Planar.rotateAround_dist (leftCenter sys) (angleA sys) x y

/-- Generator B preserves distances on the right disk -/
theorem genB_isometry_on_rightDisk : ∀ x ∈ rightDisk sys, ∀ y ∈ rightDisk sys,
    dist (sys.genB x) (sys.genB y) = dist x y := by
  intro x hx y hy
  unfold genB
  -- Both x and y are in rightDisk, so the if conditions are true
  simp only [hx, hy, ite_true]
  -- rotateAround preserves distances
  exact Planar.rotateAround_dist (rightCenter sys) (angleB sys) x y

/-- Generator A is the identity on the complement of the left disk -/
theorem genA_eq_id_on_compl : ∀ x ∉ leftDisk sys, sys.genA x = x := by
  intro x hx
  unfold genA
  simp [hx]

/-- Generator B is the identity on the complement of the right disk -/
theorem genB_eq_id_on_compl : ∀ x ∉ rightDisk sys, sys.genB x = x := by
  intro x hx
  unfold genB
  simp [hx]

/-- Convert generator A to a piecewise isometry -/
noncomputable def toPiecewiseIsometry_a : PiecewiseIsometry ℝ² where
  partition := partitionA sys
  partition_measurable := partitionA_measurable sys
  partition_countable := partitionA_countable sys
  partition_cover := partitionA_cover sys
  partition_disjoint := partitionA_disjoint sys
  partition_nonempty := partitionA_nonempty sys
  toFun := sys.genA
  isometry_on_pieces := by
    intro s hs x hx y hy
    unfold partitionA at hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · -- s = leftDisk: genA is isometric on leftDisk
      exact genA_isometry_on_leftDisk sys x hx y hy
    · -- s = leftDisk^c: genA is identity on leftDisk^c
      simp only [Set.mem_compl_iff] at hx hy
      rw [genA_eq_id_on_compl sys x hx, genA_eq_id_on_compl sys y hy]

/-- Convert generator B to a piecewise isometry -/
noncomputable def toPiecewiseIsometry_b : PiecewiseIsometry ℝ² where
  partition := partitionB sys
  partition_measurable := partitionB_measurable sys
  partition_countable := partitionB_countable sys
  partition_cover := partitionB_cover sys
  partition_disjoint := partitionB_disjoint sys
  partition_nonempty := partitionB_nonempty sys
  toFun := sys.genB
  isometry_on_pieces := by
    intro s hs x hx y hy
    unfold partitionB at hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · -- s = rightDisk: genB is isometric on rightDisk
      exact genB_isometry_on_rightDisk sys x hx y hy
    · -- s = rightDisk^c: genB is identity on rightDisk^c
      simp only [Set.mem_compl_iff] at hx hy
      rw [genB_eq_id_on_compl sys x hx, genB_eq_id_on_compl sys y hy]

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
