/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.LinearAlgebra.Orientation

/-!
# Planar Rotations

This file defines rotations about arbitrary points in the Euclidean plane ℝ².

## Main definitions

- `rotateAround`: Rotation about an arbitrary point in ℝ²
- `rotation2D`: The standard rotation about the origin in ℝ²

## Main results

- `rotateAround_dist`: Rotations preserve distances
- `rotateAround_comp`: Composition of rotations about the same point
- `rotateAround_origin`: Rotation about origin equals standard rotation
- `rotateAround_involutive`: Rotation by angle θ is inverted by -θ

## References

* Two-Disk Compound Symmetry Groups paper (arXiv:2302.12950v1)
-/

open scoped RealInnerProductSpace

namespace Planar

/-- The standard 2-dimensional Euclidean space -/
scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The standard orientation on ℝ² -/
noncomputable instance : Module.Oriented ℝ ℝ² (Fin 2) :=
  Module.Oriented.mk
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- Get the standard orientation on ℝ² -/
noncomputable def standardOrientation : Orientation ℝ ℝ² (Fin 2) :=
  Module.Oriented.positiveOrientation

/-- ℝ² has dimension 2 -/
instance : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- A rotation by angle θ about the origin in ℝ² -/
noncomputable def rotation2D (θ : Real.Angle) : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  Orientation.rotation standardOrientation θ

/-- Translation by a vector v in ℝ² -/
noncomputable def translate (v : ℝ²) : ℝ² ≃ᵃⁱ[ℝ] ℝ² :=
  AffineIsometryEquiv.constVAdd ℝ ℝ² v

/-- Rotation by angle θ about an arbitrary point c in ℝ² -/
noncomputable def rotateAround (c : ℝ²) (θ : Real.Angle) :
    ℝ² ≃ᵃⁱ[ℝ] ℝ² :=
  (translate (-c)).trans <|
    (rotation2D θ).toAffineIsometryEquiv.trans <|
      translate c

/-- Rotation about a point preserves distances -/
theorem rotateAround_dist (c : ℝ²) (θ : Real.Angle) (x y : ℝ²) :
    dist (rotateAround c θ x) (rotateAround c θ y) = dist x y :=
  (rotateAround c θ).toAffineIsometry.dist_map x y

/-- The rotation function applied to a point -/
theorem rotateAround_apply (c : ℝ²) (θ : Real.Angle) (x : ℝ²) :
    rotateAround c θ x = c + rotation2D θ (x - c) := by
  unfold rotateAround translate rotation2D
  simp [AffineIsometryEquiv.coe_trans,
    AffineIsometryEquiv.coe_constVAdd]
  abel

/-- Composition of rotations about the same point -/
theorem rotateAround_comp (c : ℝ²) (θ₁ θ₂ : Real.Angle) :
    (rotateAround c θ₁).trans (rotateAround c θ₂) =
      rotateAround c (θ₁ + θ₂) := by
  ext x
  simp only [AffineIsometryEquiv.coe_trans, rotateAround_apply,
    Function.comp_apply]
  simp only [add_sub_cancel_left]
  unfold rotation2D
  rw [← LinearIsometryEquiv.trans_apply]
  rw [Orientation.rotation_trans]
  abel

/-- Rotation about the origin equals the standard rotation -/
theorem rotateAround_origin (θ : Real.Angle) (x : ℝ²) :
    rotateAround 0 θ x = rotation2D θ x := by
  rw [rotateAround_apply]
  simp

/-- Rotation by zero angle is the identity -/
theorem rotateAround_zero (c : ℝ²) :
    rotateAround c 0 = AffineIsometryEquiv.refl ℝ ℝ² := by
  unfold rotateAround translate rotation2D
  rw [Orientation.rotation_zero]
  ext x
  simp [LinearIsometryEquiv.coe_refl]

/-- Rotation by angle θ is inverted by rotation by -θ -/
theorem rotateAround_neg (c : ℝ²) (θ : Real.Angle) :
    (rotateAround c θ).trans (rotateAround c (-θ)) =
      AffineIsometryEquiv.refl ℝ ℝ² := by
  rw [rotateAround_comp]
  simp [rotateAround_zero]

/-- The inverse of a rotation is rotation by the opposite angle -/
theorem rotateAround_symm (c : ℝ²) (θ : Real.Angle) :
    (rotateAround c θ).symm = rotateAround c (-θ) := by
  apply AffineIsometryEquiv.ext
  intro x
  apply (rotateAround c θ).injective
  simp only [AffineIsometryEquiv.apply_symm_apply]
  have h : (rotateAround c (-θ)).trans (rotateAround c (-(-θ))) =
      AffineIsometryEquiv.refl ℝ ℝ² :=
    rotateAround_neg c (-θ)
  simp at h
  rw [AffineIsometryEquiv.ext_iff] at h
  specialize h x
  simp [AffineIsometryEquiv.coe_trans] at h
  exact h.symm

/-- The center point is fixed by rotation -/
theorem rotateAround_center (c : ℝ²) (θ : Real.Angle) :
    rotateAround c θ c = c := by
  rw [rotateAround_apply]
  simp

/-- Iterating rotations composes angles -/
lemma rotateAround_iterate_aux (c : ℝ²) (θ : ℝ) (n : ℕ) :
    (rotateAround c (θ : Real.Angle))^[n] =
      (rotateAround c ((n : ℝ) * θ : Real.Angle) : ℝ² → ℝ²) := by
  induction n with
  | zero =>
      ext x
      simp [Function.iterate_zero, rotateAround_zero,
        Nat.cast_zero, zero_mul]
  | succ n' ih =>
      have angle_eq :
          ((n' : ℝ) * θ : Real.Angle) + (θ : Real.Angle) =
          (((n' : ℝ) + 1) * θ : Real.Angle) := by
        rw [← Real.Angle.coe_add]
        congr 1
        ring
      simp only [Function.iterate_succ', Function.comp, ih]
      funext x
      have comp_eq :=
        rotateAround_comp c ((n' : ℝ) * θ : Real.Angle)
          (θ : Real.Angle)
      have := congrFun (congrArg DFunLike.coe comp_eq) x
      simp only [AffineIsometryEquiv.coe_trans,
        Function.comp_apply] at this ⊢
      rw [this, angle_eq]
      congr 1
      simp only [Nat.cast_succ]

/-- Rotating n times by 2π/n gives the identity (for positive n) -/
theorem rotateAround_periodic (c : ℝ²) (n : ℕ) (hn : 0 < n) :
    (rotateAround c (2 * Real.pi / n : ℝ))^[n] = id := by
  rw [rotateAround_iterate_aux]
  ext x
  rw [rotateAround_apply]
  simp only [rotation2D, id_eq]
  have angle_calc : (n : ℝ) * (2 * Real.pi / (n : ℝ)) =
      2 * Real.pi := by
    field_simp
  rw [angle_calc, Real.Angle.coe_two_pi, Orientation.rotation_zero]
  simp [LinearIsometryEquiv.coe_refl]

end Planar
