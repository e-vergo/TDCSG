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

/-- Center of the left disk in complex plane: -1. -/
def leftCenter : ℂ := -1

/-- Center of the right disk in complex plane: 1. -/
def rightCenter : ℂ := 1

/-- DEPRECATED: Left center in Plane coordinates. Use leftCenter : ℂ instead. -/
def leftCenterPlane : Plane :=
  fun i => if i = 0 then -1 else 0

/-- DEPRECATED: Right center in Plane coordinates. Use rightCenter : ℂ instead. -/
def rightCenterPlane : Plane :=
  fun i => if i = 0 then 1 else 0

/-! ### Disk Definitions -/

/-- A closed disk in complex plane with given center and radius. -/
def closedDiskC (c : ℂ) (r : ℝ) : Set ℂ := {z | ‖z - c‖ ≤ r}

/-- The left disk in ℂ with radius r centered at -1. -/
def leftDisk (r : ℝ) : Set ℂ := closedDiskC (-1) r

/-- The right disk in ℂ with radius r centered at 1. -/
def rightDisk (r : ℝ) : Set ℂ := closedDiskC 1 r

/-- DEPRECATED: A closed disk in Plane. Use closedDiskC instead. -/
def closedDisk (center : Plane) (radius : ℝ) : Set Plane :=
  Metric.closedBall center radius

/-- DEPRECATED: Left disk in Plane. Use leftDisk : Set ℂ instead. -/
noncomputable def leftDiskPlane (r : ℝ) : Set Plane := closedDisk leftCenterPlane r

/-- DEPRECATED: Right disk in Plane. Use rightDisk : Set ℂ instead. -/
noncomputable def rightDiskPlane (r : ℝ) : Set Plane := closedDisk rightCenterPlane r

/-! ### Rotation Operations -/

/-- Rotation in the complex plane about a center by angle θ. -/
noncomputable def rotateAboutC (c : ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  c + Complex.exp (θ * Complex.I) * (z - c)

/-- DEPRECATED: Rotation matrix in R^2 by angle theta. -/
noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

/-- DEPRECATED: Apply a 2x2 matrix to a point in R^2. -/
noncomputable def applyMatrix (M : Matrix (Fin 2) (Fin 2) ℝ) (p : Plane) : Plane :=
  fun i => ∑ j, M i j * p j

/-- DEPRECATED: Rotation about a given center point by angle theta.
    Use rotateAboutC for complex plane rotations. -/
noncomputable def rotateAroundPoint (center : Plane) (θ : ℝ) (p : Plane) : Plane :=
  center + applyMatrix (rotationMatrix θ) (p - center)

end TDCSG.Definitions
