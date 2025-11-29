/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic

/-!
# Geometric Definitions - Disks and Rotations

This file defines the two-disk geometry with FIXED centers at (-1, 0) and (1, 0).
The radius parameter determines disk size, not center position.

## Main definitions
- `leftCenter`, `rightCenter` : Fixed disk centers at (-1, 0) and (1, 0)
- `closedDisk`, `leftDisk`, `rightDisk` : Disk sets
- `rotationMatrix`, `applyMatrix`, `rotateAround` : Rotation operations
- `toPlane` : Convert a complex number to a Plane point

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

/-! ### Complex to Plane Conversion -/

/-- Convert a complex number to a Plane point (EuclideanSpace form). -/
noncomputable def toPlane (z : ℂ) : Plane := ![z.re, z.im]

/-- Addition in complex numbers corresponds to addition in Plane. -/
lemma toPlane_add (z w : ℂ) : toPlane (z + w) = toPlane z + toPlane w := by
  unfold toPlane
  ext i
  fin_cases i <;> simp [Complex.add_re, Complex.add_im]

/-- Subtraction in complex numbers corresponds to subtraction in Plane. -/
lemma toPlane_sub (z w : ℂ) : toPlane (z - w) = toPlane z - toPlane w := by
  unfold toPlane
  ext i
  fin_cases i <;> simp [Complex.sub_re, Complex.sub_im]

/-- Distance in Plane equals complex norm. -/
lemma toPlane_dist_eq_complex_norm (z w : ℂ) : dist (toPlane z) (toPlane w) = ‖z - w‖ := by
  unfold toPlane
  rw [dist_comm, EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dist_comm (w.re), dist_comm (w.im)]
  simp only [Real.dist_eq]
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.sub_re, Complex.sub_im]
  congr 1
  simp only [sq_abs]

/-- leftCenter equals toPlane (-1). -/
lemma leftCenter_eq_toPlane : leftCenter = toPlane (-1 : ℂ) := by
  unfold leftCenter toPlane
  ext i
  fin_cases i <;> simp [Complex.neg_re, Complex.neg_im]

/-- rightCenter equals toPlane (1). -/
lemma rightCenter_eq_toPlane : rightCenter = toPlane (1 : ℂ) := by
  unfold rightCenter toPlane
  ext i
  fin_cases i <;> simp [Complex.one_re, Complex.one_im]

end TDCSG.Definitions
