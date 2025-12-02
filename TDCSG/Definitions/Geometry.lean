import TDCSG.Definitions.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.Real.GoldenRatio

namespace TDCSG.Definitions

open Real

def leftCenter : ℂ := -1

def rightCenter : ℂ := 1

def closedDiskC (c : ℂ) (r : ℝ) : Set ℂ := {z | ‖z - c‖ ≤ r}

def leftDisk (r : ℝ) : Set ℂ := closedDiskC (-1) r

def rightDisk (r : ℝ) : Set ℂ := closedDiskC 1 r

noncomputable def rotateAboutC (c : ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  c + Complex.exp (θ * Complex.I) * (z - c)

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

lemma rotateAboutCircle_inv (c : ℂ) (a : Circle) (z : ℂ) :
    rotateAboutCircle c a⁻¹ (rotateAboutCircle c a z) = z := by
  simp only [rotateAboutCircle, Circle.coe_inv]
  have h : (a : ℂ) ≠ 0 := Circle.coe_ne_zero a
  field_simp [h]
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

noncomputable def genA_n (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ leftDisk r then rotateAboutC leftCenter (-2 * π / n) z else z

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
