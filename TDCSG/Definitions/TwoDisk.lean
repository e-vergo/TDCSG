/-
Copyright (c) 2025 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Rotations
import TDCSG.Disks
import TDCSG.Definitions.Geometry
import TDCSG.Definitions.PiecewiseIsometry

/-!
# Two-Disk System Definitions

This file contains the core definitions for the two-disk compound symmetry group construction.

## Main definitions

- `TwoDiskSystem`: Two disks with specified radii and rotation orders
- `TwoDiskSystem.diskL`: The left disk in the system
- `TwoDiskSystem.diskR`: The right disk in the system
- `TwoDiskSystem.exterior`: The exterior region (outside both disks)
- `TwoDiskSystem.angleA`: The rotation angle for the left disk
- `TwoDiskSystem.angleB`: The rotation angle for the right disk
- `TwoDiskSystem.rotationA`: Rotation A (on left disk)
- `TwoDiskSystem.rotationB`: Rotation B (on right disk)
- `TwoDiskSystem.partitionA`: The partition for generator A
- `TwoDiskSystem.partitionB`: The partition for generator B
- `TwoDiskSystem.basicPartition`: The initial partition

## References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)

-/

open scoped RealInnerProductSpace
open Planar
open Classical
open TDCSG.Definitions

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

/-- The left disk (method on TwoDiskSystem) -/
noncomputable def diskL : Set ℝ² :=
  Disk leftCenter sys.r1

/-- The right disk (method on TwoDiskSystem) -/
noncomputable def diskR : Set ℝ² :=
  Disk rightCenter sys.r2

/-- The exterior region (outside both disks) -/
noncomputable def exterior : Set ℝ² :=
  (diskL sys ∪ diskR sys)ᶜ

/-- The rotation angle for the left disk generator -/
noncomputable def angleA : Real.Angle :=
  (2 * Real.pi / sys.n1 : ℝ)

/-- The rotation angle for the right disk generator -/
noncomputable def angleB : Real.Angle :=
  (2 * Real.pi / sys.n2 : ℝ)

/-- Rotation A: rotation by 2π/n1 around the center of the left disk.
    This is the TwoDiskSystem version; see MainTheorem.genA for the simplified theorem API. -/
noncomputable def rotationA : ℝ² → ℝ² :=
  fun x => if x ∈ diskL sys then
    rotateAround leftCenter (angleA sys) x
  else
    x

/-- Rotation B: rotation by 2π/n2 around the center of the right disk.
    This is the TwoDiskSystem version; see MainTheorem.genB for the simplified theorem API. -/
noncomputable def rotationB : ℝ² → ℝ² :=
  fun x => if x ∈ diskR sys then
    rotateAround rightCenter (angleB sys) x
  else
    x

/-- The partition for generator A. -/
noncomputable def partitionA : Set (Set ℝ²) :=
  {diskL sys, (diskL sys)ᶜ}

/-- The partition for generator B. -/
noncomputable def partitionB : Set (Set ℝ²) :=
  {diskR sys, (diskR sys)ᶜ}

/-- The basic partition for the two-disk system. -/
noncomputable def basicPartition : Set (Set ℝ²) :=
  {diskL sys, diskR sys, exterior sys}

/-- Convert generator A to a piecewise isometry.
    The isometry_on_pieces proof is provided in TDCSG.TwoDisk. -/
noncomputable def toPiecewiseIsometry_a : PiecewiseIsometry ℝ² where
  partition := partitionA sys
  partition_measurable := sorry
  partition_countable := sorry
  partition_cover := sorry
  partition_disjoint := sorry
  partition_nonempty := sorry
  toFun := rotationA sys
  isometry_on_pieces := sorry

/-- Convert generator B to a piecewise isometry.
    The isometry_on_pieces proof is provided in TDCSG.TwoDisk. -/
noncomputable def toPiecewiseIsometry_b : PiecewiseIsometry ℝ² where
  partition := partitionB sys
  partition_measurable := sorry
  partition_countable := sorry
  partition_cover := sorry
  partition_disjoint := sorry
  partition_nonempty := sorry
  toFun := rotationB sys
  isometry_on_pieces := sorry

end TwoDiskSystem

end CompoundSymmetry
