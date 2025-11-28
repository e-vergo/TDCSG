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
# Planar Rotation Definitions

This file defines rotations about arbitrary points in the Euclidean plane R^2.

## Main definitions

- `standardOrientation`: The standard orientation on R^2
- `rotation2D`: The standard rotation about the origin in R^2
- `translate`: Translation by a vector in R^2
- `rotateAround`: Rotation about an arbitrary point in R^2

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

/-- Rotation about an arbitrary point c by angle θ in ℝ².
    This is: translate to origin, rotate, translate back. -/
noncomputable def rotateAround (c : ℝ²) (θ : Real.Angle) : ℝ² ≃ᵃⁱ[ℝ] ℝ² :=
  (translate (-c)).trans ((rotation2D θ).toAffineIsometryEquiv.trans (translate c))

end Planar
