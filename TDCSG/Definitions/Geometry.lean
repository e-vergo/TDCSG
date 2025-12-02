/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.Real.GoldenRatio

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
def leftCenter : ℂ := -1

/-- Center of the right disk in complex plane: (1, 0). -/
def rightCenter : ℂ := 1

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

/-- Rotation about a center preserves membership in a disk centered at that point.
    Key fact: rotation by a unit complex number preserves distance from the center. -/
lemma rotateAboutCircle_preserves_disk (c : ℂ) (a : Circle) (r : ℝ) (z : ℂ)
    (hz : z ∈ closedDiskC c r) : rotateAboutCircle c a z ∈ closedDiskC c r := by
  unfold closedDiskC at hz ⊢
  simp only [Set.mem_setOf_eq] at hz ⊢
  -- rotateAboutCircle c a z - c = a * (z - c)
  have h_eq : rotateAboutCircle c a z - c = a * (z - c) := by
    unfold rotateAboutCircle
    ring
  rw [h_eq, Complex.norm_mul]
  -- ‖a‖ = 1 for a ∈ Circle
  rw [Circle.norm_coe, one_mul]
  exact hz

/-! ### N-fold Generalized Generators

The generators A_n and B_n are piecewise isometries that rotate by -2pi/n
(clockwise) inside their respective disks and act as the identity outside.

For n >= 1, these satisfy (A_n)^n = (B_n)^n = id, making them order-n elements.
The 5-fold case (n=5) is what we study in GG5.
-/

/-- Generalized generator A_n: rotation by -2pi/n (clockwise) about the left disk center (-1).
    Acts as the identity outside the left disk.

    For n >= 1, this is an order-n element: (genA_n n r)^n = id.
    The original genA used throughout the codebase is genA_n 5. -/
noncomputable def genA_n (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ leftDisk r then rotateAboutC leftCenter (-2 * π / n) z else z

/-- Generalized generator B_n: rotation by -2pi/n (clockwise) about the right disk center (1).
    Acts as the identity outside the right disk.

    For n >= 1, this is an order-n element: (genB_n n r)^n = id.
    The original genB used throughout the codebase is genB_n 5. -/
noncomputable def genB_n (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ rightDisk r then rotateAboutC rightCenter (-2 * π / n) z else z

end TDCSG.Definitions

/-!
## Two-Disk System

A two-disk system with specified radii and rotation orders.

### References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)
-/

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
