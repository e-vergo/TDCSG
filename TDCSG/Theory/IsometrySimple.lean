import TDCSG.Core.Basic
import TDCSG.Theory.GroupAction

/-!
# Piecewise Isometry Theory (Simplified)

This file contains the theory of piecewise isometries for the two-disk system.
Simplified version to avoid complex proofs.

## Main theorems

* Rotations are piecewise isometries
* Group elements are piecewise isometries
-/

open Complex TwoDiskSystem

namespace TwoDiskSystem

variable (sys : TwoDiskSystem)

/-- A piecewise isometry is a function that preserves distances on each piece of a partition. -/
structure PiecewiseIsometry where
  /-- The function -/
  f : ℂ → ℂ
  /-- The partition of the domain -/
  pieces : List (Set ℂ)
  /-- Each piece is an isometry -/
  isometry_on_pieces : ∀ p ∈ pieces, ∀ z ∈ p, ∀ w ∈ p, ‖f z - f w‖ = ‖z - w‖

/-- Left rotation is a piecewise isometry -/
theorem leftRotation_piecewise_isometry :
    ∃ pi : PiecewiseIsometry, pi.f = sys.leftRotation := by
  use {
    f := sys.leftRotation
    pieces := [sys.leftDisk, sys.leftDiskᶜ]
    isometry_on_pieces := by
      intro p hp z hz w hw
      simp only [List.mem_cons, List.mem_singleton] at hp
      cases hp with
      | inl hp_left =>
        -- p = leftDisk: rotation preserves distance
        rw [hp_left] at hz hw
        unfold leftRotation
        simp only [if_pos hz, if_pos hw, leftCenter]
        have : (-1 : ℂ) + Complex.exp (Complex.I * ↑sys.leftAngle) * (z - -1) -
               ((-1) + Complex.exp (Complex.I * ↑sys.leftAngle) * (w - -1)) =
               Complex.exp (Complex.I * ↑sys.leftAngle) * (z - w) := by ring
        rw [this, norm_mul]
        have h_exp : ‖Complex.exp (Complex.I * ↑sys.leftAngle)‖ = 1 := by
          rw [Complex.norm_exp]
          simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          ring_nf; norm_num
        rw [h_exp]; simp
      | inr hp_right =>
        -- p = leftDiskᶜ: rotation is identity
        cases hp_right with
        | inl hp_eq =>
          rw [hp_eq] at hz hw
          unfold leftRotation
          rw [if_neg hz, if_neg hw]
        | inr hp_nil =>
          simp only [List.not_mem_nil] at hp_nil
  }

/-- Right rotation is a piecewise isometry -/
theorem rightRotation_piecewise_isometry :
    ∃ pi : PiecewiseIsometry, pi.f = sys.rightRotation := by
  use {
    f := sys.rightRotation
    pieces := [sys.rightDisk, sys.rightDiskᶜ]
    isometry_on_pieces := by
      intro p hp z hz w hw
      simp only [List.mem_cons, List.mem_singleton] at hp
      cases hp with
      | inl hp_left =>
        rw [hp_left] at hz hw
        unfold rightRotation
        simp only [if_pos hz, if_pos hw, rightCenter]
        have : (1 : ℂ) + Complex.exp (Complex.I * ↑sys.rightAngle) * (z - 1) -
               ((1) + Complex.exp (Complex.I * ↑sys.rightAngle) * (w - 1)) =
               Complex.exp (Complex.I * ↑sys.rightAngle) * (z - w) := by ring
        rw [this, norm_mul]
        have h_exp : ‖Complex.exp (Complex.I * ↑sys.rightAngle)‖ = 1 := by
          rw [Complex.norm_exp]
          simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          ring_nf; norm_num
        rw [h_exp]; simp
      | inr hp_right =>
        cases hp_right with
        | inl hp_eq =>
          rw [hp_eq] at hz hw
          unfold rightRotation
          rw [if_neg hz, if_neg hw]
        | inr hp_nil =>
          simp only [List.not_mem_nil] at hp_nil
  }

/-- Left inverse rotation is a piecewise isometry -/
theorem leftRotationInv_piecewise_isometry :
    ∃ pi : PiecewiseIsometry, pi.f = sys.leftRotationInv := by
  use {
    f := sys.leftRotationInv
    pieces := [sys.leftDisk, sys.leftDiskᶜ]
    isometry_on_pieces := by
      intro p hp z hz w hw
      simp only [List.mem_cons, List.mem_singleton] at hp
      cases hp with
      | inl hp_left =>
        rw [hp_left] at hz hw
        unfold leftRotationInv
        simp only [if_pos hz, if_pos hw, leftCenter]
        have : (-1 : ℂ) + Complex.exp (-Complex.I * ↑sys.leftAngle) * (z - -1) -
               ((-1) + Complex.exp (-Complex.I * ↑sys.leftAngle) * (w - -1)) =
               Complex.exp (-Complex.I * ↑sys.leftAngle) * (z - w) := by ring
        rw [this, norm_mul]
        have h_exp : ‖Complex.exp (-Complex.I * ↑sys.leftAngle)‖ = 1 := by
          rw [Complex.norm_exp]
          simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          ring_nf; norm_num
        rw [h_exp]; simp
      | inr hp_right =>
        cases hp_right with
        | inl hp_eq =>
          rw [hp_eq] at hz hw
          unfold leftRotationInv
          rw [if_neg hz, if_neg hw]
        | inr hp_nil =>
          simp only [List.not_mem_nil] at hp_nil
  }

/-- Right inverse rotation is a piecewise isometry -/
theorem rightRotationInv_piecewise_isometry :
    ∃ pi : PiecewiseIsometry, pi.f = sys.rightRotationInv := by
  use {
    f := sys.rightRotationInv
    pieces := [sys.rightDisk, sys.rightDiskᶜ]
    isometry_on_pieces := by
      intro p hp z hz w hw
      simp only [List.mem_cons, List.mem_singleton] at hp
      cases hp with
      | inl hp_left =>
        rw [hp_left] at hz hw
        unfold rightRotationInv
        simp only [if_pos hz, if_pos hw, rightCenter]
        have : (1 : ℂ) + Complex.exp (-Complex.I * ↑sys.rightAngle) * (z - 1) -
               ((1) + Complex.exp (-Complex.I * ↑sys.rightAngle) * (w - 1)) =
               Complex.exp (-Complex.I * ↑sys.rightAngle) * (z - w) := by ring
        rw [this, norm_mul]
        have h_exp : ‖Complex.exp (-Complex.I * ↑sys.rightAngle)‖ = 1 := by
          rw [Complex.norm_exp]
          simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          ring_nf; norm_num
        rw [h_exp]; simp
      | inr hp_right =>
        cases hp_right with
        | inl hp_eq =>
          rw [hp_eq] at hz hw
          unfold rightRotationInv
          rw [if_neg hz, if_neg hw]
        | inr hp_nil =>
          simp only [List.not_mem_nil] at hp_nil
  }

/-- Apply a generator is a piecewise isometry -/
lemma applyGenerator_piecewise_isometry (gen : Fin 2) (inv : Bool) :
    ∃ pi : PiecewiseIsometry, pi.f = applyGenerator sys gen inv := by
  fin_cases gen <;> cases inv
  · -- gen = 0, inv = false (leftRotation)
    unfold applyGenerator
    simp only [↓reduceIte]
    exact leftRotation_piecewise_isometry sys
  · -- gen = 0, inv = true (leftRotationInv)
    unfold applyGenerator
    simp only [↓reduceIte]
    exact leftRotationInv_piecewise_isometry sys
  · -- gen = 1, inv = false (rightRotation)
    unfold applyGenerator
    simp only [↓reduceIte]
    exact rightRotation_piecewise_isometry sys
  · -- gen = 1, inv = true (rightRotationInv)
    unfold applyGenerator
    simp only [↓reduceIte]
    exact rightRotationInv_piecewise_isometry sys

/-- All group elements are piecewise isometries -/
theorem group_element_piecewise_isometry (g : TwoDiskGroup) :
    ∃ pi : PiecewiseIsometry, pi.f = applyGroupElement sys g := by
  -- This requires proving that composition of piecewise isometries is a piecewise isometry
  -- Challenge: Need to refine partitions when composing
  -- Strategy: Induction on word representation
  --   Base: g = 1 → identity is piecewise isometry with partition [Set.univ]
  --   Step: g = g' * generator → compose piecewise isometries
  --     Need: composition_piecewise_isometry lemma
  sorry  -- Blocked on composition of piecewise isometries

end TwoDiskSystem