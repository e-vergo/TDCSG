/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Geometric Definitions

This file defines the geometric objects and transformations for the two-disk system,
including disk regions, rotation operations, and the piecewise isometry generators.

## Main definitions

- `leftCenter`, `rightCenter`: The centers of the two disks at -1 and +1
- `leftDisk r`, `rightDisk r`: Closed disks of radius r centered at ±1
- `rotateAboutC c θ z`: Rotate point z by angle θ about center c
- `rotateAboutCircle c a z`: Rotate point z by circle element a about center c
- `genA_n n r`: The n-fold generator A (rotates by -2π/n inside left disk, identity outside)
- `genB_n n r`: The n-fold generator B (rotates by -2π/n inside right disk, identity outside)

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open Real

/-- The center of the left disk at -1. -/
def leftCenter : ℂ := -1

/-- The center of the right disk at +1. -/
def rightCenter : ℂ := 1

/-- Closed disk of radius r centered at c in the complex plane. -/
def closedDiskC (c : ℂ) (r : ℝ) : Set ℂ := {z | ‖z - c‖ ≤ r}

/-- The left disk of radius r centered at -1. -/
def leftDisk (r : ℝ) : Set ℂ := closedDiskC (-1) r

/-- The right disk of radius r centered at +1. -/
def rightDisk (r : ℝ) : Set ℂ := closedDiskC 1 r

/-- Rotate point z by angle θ about center c. -/
noncomputable def rotateAboutC (c : ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  c + Complex.exp (θ * Complex.I) * (z - c)

/-- Rotate point z by circle element a about center c. -/
def rotateAboutCircle (c : ℂ) (a : Circle) (z : ℂ) : ℂ :=
  c + a * (z - c)

lemma rotateAboutCircle_eq_rotateAboutC (c : ℂ) (θ : ℝ) (z : ℂ) :
    rotateAboutCircle c (Circle.exp θ) z = rotateAboutC c θ z := by
  simp only [rotateAboutCircle, rotateAboutC, Circle.coe_exp]

lemma rotateAboutCircle_one (c z : ℂ) : rotateAboutCircle c 1 z = z := by
  simp [rotateAboutCircle]

lemma rotateAboutCircle_mul (c : ℂ) (a b : Circle) (z : ℂ) :
    rotateAboutCircle c (a * b) z = rotateAboutCircle c a (rotateAboutCircle c b z) := by
  simp only [rotateAboutCircle, Circle.coe_mul]
  ring

lemma rotateAboutCircle_pow (c : ℂ) (a : Circle) (n : ℕ) (z : ℂ) :
    (rotateAboutCircle c a)^[n] z = rotateAboutCircle c (a ^ n) z := by
  induction n with
  | zero => simp [rotateAboutCircle_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ, mul_comm]
    exact (rotateAboutCircle_mul c a (a ^ n) z).symm

lemma rotateAboutCircle_preserves_disk (c : ℂ) (a : Circle) (r : ℝ) (z : ℂ)
    (hz : z ∈ closedDiskC c r) : rotateAboutCircle c a z ∈ closedDiskC c r := by
  unfold closedDiskC at hz ⊢
  simp only [Set.mem_setOf_eq] at hz ⊢

  have h_eq : rotateAboutCircle c a z - c = a * (z - c) := by
    unfold rotateAboutCircle
    ring
  rw [h_eq, Complex.norm_mul]

  rw [Circle.norm_coe, one_mul]
  exact hz

/-- The n-fold generator A at radius r: rotates by -2π/n about -1 inside the left disk,
acts as identity outside. This is a piecewise isometry on ℂ. -/
noncomputable def genA_n (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ leftDisk r then rotateAboutC leftCenter (-2 * π / n) z else z

/-- The n-fold generator B at radius r: rotates by -2π/n about +1 inside the right disk,
acts as identity outside. This is a piecewise isometry on ℂ. -/
noncomputable def genB_n (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ rightDisk r then rotateAboutC rightCenter (-2 * π / n) z else z

end TDCSG.Definitions

namespace CompoundSymmetry

structure TwoDiskSystem where

  r1 : ℝ

  r2 : ℝ

  n1 : ℕ

  n2 : ℕ

end CompoundSymmetry
