/-
Copyright (c) 2025 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.Geometry

/-!
# Two-Disk System Definitions

This file contains the core definitions for the two-disk compound symmetry group construction.

## Main definitions

- `TwoDiskSystem`: Two disks with specified radii and rotation orders
- `TwoDiskSystem.diskL`: The left disk in the system (in ℂ)
- `TwoDiskSystem.diskR`: The right disk in the system (in ℂ)
- `TwoDiskSystem.exterior`: The exterior region (outside both disks)
- `TwoDiskSystem.angleA`: The rotation angle for the left disk
- `TwoDiskSystem.angleB`: The rotation angle for the right disk
- `TwoDiskSystem.rotationA`: Rotation A (on left disk)
- `TwoDiskSystem.rotationB`: Rotation B (on right disk)

## Note

All definitions use ℂ as the primary representation.

## References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)

-/

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

/-- The left disk in ℂ (method on TwoDiskSystem) -/
def diskL : Set ℂ := leftDisk sys.r1

/-- The right disk in ℂ (method on TwoDiskSystem) -/
def diskR : Set ℂ := rightDisk sys.r2

/-- The exterior region (outside both disks) -/
def exterior : Set ℂ := (diskL sys ∪ diskR sys)ᶜ

/-- The rotation angle for the left disk generator (in radians) -/
noncomputable def angleA : ℝ := 2 * Real.pi / sys.n1

/-- The rotation angle for the right disk generator (in radians) -/
noncomputable def angleB : ℝ := 2 * Real.pi / sys.n2

/-- Rotation A: rotation by 2π/n1 around the center of the left disk in ℂ.
    This is the TwoDiskSystem version; see GroupAction.genA for the simplified theorem API. -/
noncomputable def rotationA (z : ℂ) : ℂ :=
  if z ∈ diskL sys then
    rotateAboutC leftCenter (angleA sys) z
  else
    z

/-- Rotation B: rotation by 2π/n2 around the center of the right disk in ℂ.
    This is the TwoDiskSystem version; see GroupAction.genB for the simplified theorem API. -/
noncomputable def rotationB (z : ℂ) : ℂ :=
  if z ∈ diskR sys then
    rotateAboutC rightCenter (angleB sys) z
  else
    z

end TwoDiskSystem

end CompoundSymmetry
