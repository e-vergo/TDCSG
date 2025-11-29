/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
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
-/

namespace TDCSG.Definitions

open Real

/-! ### Disk Centers (FIXED positions) -/

/-- Center of the left disk in complex plane: (-1, 0). -/
def leftCenter : ℂ := -1 + 0 * Complex.I

/-- Center of the right disk in complex plane: (1, 0). -/
def rightCenter : ℂ := 1 + 0 * Complex.I

/-! ### Disk Definitions -/

/-- A closed disk in complex plane with given center and radius. -/
def closedDiskC (c : ℂ) (r : ℝ) : Set ℂ := {z | ‖z - c‖ ≤ r}

/-- The left disk in ℂ with radius r centered at -1. -/
def leftDisk (r : ℝ) : Set ℂ := closedDiskC (-1) r

/-- The right disk in ℂ with radius r centered at 1. -/
def rightDisk (r : ℝ) : Set ℂ := closedDiskC 1 r

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

end TDCSG.Definitions
