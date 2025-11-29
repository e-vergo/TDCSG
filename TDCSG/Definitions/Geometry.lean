/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Circle

/-!
# Geometric Definitions - Disks and Rotations

This file defines the two-disk geometry with FIXED centers at (-1, 0) and (1, 0).
The radius parameter determines disk size, not center position.

## Main definitions
- `leftCenter`, `rightCenter` : Fixed disk centers at (-1, 0) and (1, 0)
- `closedDisk`, `leftDisk`, `rightDisk` : Disk sets
- `rotateAboutC` : Rotation by angle θ about a center
- `rotateAboutCircle` : Rotation using Circle element (unit complex number)
- `toPlane` : Convert a complex number to a Plane point

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

/-- Rotation about a center using a Circle element (unit complex number).
    This is simpler than angle-based rotation and leverages Circle's group structure. -/
def rotateAboutCircle (c : ℂ) (a : Circle) (z : ℂ) : ℂ :=
  c + a * (z - c)

/-- rotateAboutCircle with Circle.exp θ equals rotateAboutC with angle θ. -/
lemma rotateAboutCircle_eq_rotateAboutC (c : ℂ) (θ : ℝ) (z : ℂ) :
    rotateAboutCircle c (Circle.exp θ) z = rotateAboutC c θ z := by
  simp only [rotateAboutCircle, rotateAboutC, Circle.coe_exp]

/-- Rotation by 1 (identity element of Circle) is the identity. -/
lemma rotateAboutCircle_one (c z : ℂ) : rotateAboutCircle c 1 z = z := by
  simp [rotateAboutCircle]

/-- Composition of rotations corresponds to multiplication in Circle. -/
lemma rotateAboutCircle_mul (c : ℂ) (a b : Circle) (z : ℂ) :
    rotateAboutCircle c (a * b) z = rotateAboutCircle c a (rotateAboutCircle c b z) := by
  simp only [rotateAboutCircle, Circle.coe_mul]
  ring

/-- Inverse rotation undoes the rotation. -/
lemma rotateAboutCircle_inv (c : ℂ) (a : Circle) (z : ℂ) :
    rotateAboutCircle c a⁻¹ (rotateAboutCircle c a z) = z := by
  simp only [rotateAboutCircle, Circle.coe_inv]
  have h : (a : ℂ) ≠ 0 := Circle.coe_ne_zero a
  field_simp [h]
  ring

/-- n-fold rotation using Circle power. -/
lemma rotateAboutCircle_pow (c : ℂ) (a : Circle) (n : ℕ) (z : ℂ) :
    (rotateAboutCircle c a)^[n] z = rotateAboutCircle c (a ^ n) z := by
  induction n with
  | zero => simp [rotateAboutCircle_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ, mul_comm]
    exact (rotateAboutCircle_mul c a (a ^ n) z).symm

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

/-- leftCenterPlane equals toPlane of leftCenter. -/
lemma leftCenterPlane_eq_toPlane : leftCenterPlane = toPlane leftCenter := by
  unfold leftCenterPlane leftCenter toPlane
  ext i
  fin_cases i <;> simp [Complex.neg_re, Complex.neg_im]

/-- rightCenterPlane equals toPlane of rightCenter. -/
lemma rightCenterPlane_eq_toPlane : rightCenterPlane = toPlane rightCenter := by
  unfold rightCenterPlane rightCenter toPlane
  ext i
  fin_cases i <;> simp [Complex.one_re, Complex.one_im]

end TDCSG.Definitions
