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

end CompoundSymmetry
