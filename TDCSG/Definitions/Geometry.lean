/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Geometric Definitions - Disks and Rotations

This file defines the two-disk geometry with FIXED centers at (-1, 0) and (1, 0).
The radius parameter determines disk size, not center position.

## Main definitions
- `leftCenter`, `rightCenter` : Fixed disk centers at (-1, 0) and (1, 0)
- `closedDisk`, `leftDisk`, `rightDisk` : Disk sets
- `rotationMatrix`, `applyMatrix`, `rotateAround` : Rotation operations

Note: `Plane` is defined in TDCSG.Definitions.Core
-/

namespace TDCSG.Definitions

open Real

/-! ### Disk Centers (FIXED positions) -/

/-- Center of the left disk, positioned at (-1, 0).
    This is a FIXED position, independent of radius. -/
def leftCenter : Plane :=
  fun i => if i = 0 then -1 else 0

/-- Center of the right disk, positioned at (1, 0).
    This is a FIXED position, independent of radius. -/
def rightCenter : Plane :=
  fun i => if i = 0 then 1 else 0

/-! ### Disk Definitions -/

/-- A closed disk in the plane with given center and radius. -/
def closedDisk (center : Plane) (radius : ℝ) : Set Plane :=
  Metric.closedBall center radius

/-- The left disk with radius r centered at (-1, 0). -/
noncomputable def leftDisk (r : ℝ) : Set Plane := closedDisk leftCenter r

/-- The right disk with radius r centered at (1, 0). -/
noncomputable def rightDisk (r : ℝ) : Set Plane := closedDisk rightCenter r

/-! ### Rotation Operations -/

/-- Rotation matrix in R^2 by angle theta. -/
noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

/-- Apply a 2x2 matrix to a point in R^2. -/
noncomputable def applyMatrix (M : Matrix (Fin 2) (Fin 2) ℝ) (p : Plane) : Plane :=
  fun i => ∑ j, M i j * p j

/-- Rotation about a given center point by angle theta.
    Returns the rotated point (simple version, not an isometry equivalence). -/
noncomputable def rotateAroundPoint (center : Plane) (θ : ℝ) (p : Plane) : Plane :=
  center + applyMatrix (rotationMatrix θ) (p - center)

end TDCSG.Definitions
