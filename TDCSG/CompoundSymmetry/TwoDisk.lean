/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Planar.Rotations
import TDCSG.Planar.Disks

/-!
# Two-Disk Compound Symmetry Groups

This file formalizes the two-disk compound symmetry group construction from the paper
"Two-Disk Compound Symmetry Groups" (arXiv:2302.12950v1).

## Main definitions

- `TwoDiskSystem`: A structure encoding two disks with specified radii and rotation orders
- `TwoDiskSystem.leftDisk`: The left disk in the system
- `TwoDiskSystem.rightDisk`: The right disk in the system
- `TwoDiskSystem.genA`: Generator A (rotation on left disk)
- `TwoDiskSystem.genB`: Generator B (rotation on right disk)
- `TwoDiskSystem.basicPartition`: The initial partition for the two-disk system
- `TwoDiskSystem.toPiecewiseIsometry_a`: Convert generator A to a piecewise isometry
- `TwoDiskSystem.toPiecewiseIsometry_b`: Convert generator B to a piecewise isometry

## Notation

- `GG_n(r)` for the single-disk group with n-fold rotation symmetry and radius r
- `GG_{n1,n2}(r1,r2)` for the two-disk compound symmetry group

## Implementation notes

We use EuclideanSpace ℝ (Fin 2) to ensure proper Euclidean distance metric.
The two disks are positioned symmetrically about the origin along the x-axis.

## References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)

-/

open scoped RealInnerProductSpace
open Planar
open Classical

namespace CompoundSymmetry

/-- A two-disk system with specified radii and rotation orders.

   The system consists of:
   - Left disk: centered at (-d, 0) with radius r1, n1-fold rotation symmetry
   - Right disk: centered at (d, 0) with radius r2, n2-fold rotation symmetry
   where d is chosen so the disks touch at the origin (d = r1 = r2 for equal radii)
-/
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

/-- The basic partition for the two-disk system -/
noncomputable def basicPartition : Set (Set ℝ²) :=
  {leftDisk sys, rightDisk sys, exterior sys}

/-- The basic partition is countable (it's finite) -/
theorem basicPartition_countable : (basicPartition sys).Countable := by
  sorry

/-- The basic partition is measurable -/
theorem basicPartition_measurable : ∀ s ∈ basicPartition sys, MeasurableSet s := by
  sorry

/-- The basic partition covers the entire plane -/
theorem basicPartition_cover : ⋃₀ basicPartition sys = Set.univ := by
  sorry

/-- The basic partition pieces are pairwise disjoint -/
theorem basicPartition_disjoint : (basicPartition sys).PairwiseDisjoint id := by
  sorry

/-- Each partition piece is nonempty -/
theorem basicPartition_nonempty : ∀ s ∈ basicPartition sys, s.Nonempty := by
  sorry

/-- Generator A preserves distances on the left disk -/
theorem genA_isometry_on_leftDisk : ∀ x ∈ leftDisk sys, ∀ y ∈ leftDisk sys,
    dist (sys.genA x) (sys.genA y) = dist x y := by
  sorry

/-- Generator B preserves distances on the right disk -/
theorem genB_isometry_on_rightDisk : ∀ x ∈ rightDisk sys, ∀ y ∈ rightDisk sys,
    dist (sys.genB x) (sys.genB y) = dist x y := by
  sorry

/-- Generator A is the identity on the complement of the left disk -/
theorem genA_eq_id_on_compl : ∀ x ∉ leftDisk sys, sys.genA x = x := by
  sorry

/-- Generator B is the identity on the complement of the right disk -/
theorem genB_eq_id_on_compl : ∀ x ∉ rightDisk sys, sys.genB x = x := by
  sorry

/-- Convert generator A to a piecewise isometry -/
noncomputable def toPiecewiseIsometry_a : PiecewiseIsometry ℝ² where
  partition := basicPartition sys
  partition_measurable := basicPartition_measurable sys
  partition_countable := basicPartition_countable sys
  partition_cover := basicPartition_cover sys
  partition_disjoint := basicPartition_disjoint sys
  partition_nonempty := basicPartition_nonempty sys
  toFun := sys.genA
  isometry_on_pieces := by sorry

/-- Convert generator B to a piecewise isometry -/
noncomputable def toPiecewiseIsometry_b : PiecewiseIsometry ℝ² where
  partition := basicPartition sys
  partition_measurable := basicPartition_measurable sys
  partition_countable := basicPartition_countable sys
  partition_cover := basicPartition_cover sys
  partition_disjoint := basicPartition_disjoint sys
  partition_nonempty := basicPartition_nonempty sys
  toFun := sys.genB
  isometry_on_pieces := by sorry

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
