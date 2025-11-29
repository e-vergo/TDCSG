/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import TDCSG.Definitions.Geometry

/-!
# Group Action Definitions

This file defines the group action for the two-disk compound symmetry groups.

## Main definitions
- `genA`, `genB` : The two generators (5-fold rotations)
- `applyGen`, `applyWord` : Application of generators and words
- `orbit` : The orbit of a point under the group action

## Note
This file uses ℂ as the primary representation.
-/

namespace TDCSG.Definitions

open Real

/-- Generator A: rotation by -2π/5 (clockwise) about the left disk center (-1).
    Acts as the identity outside the left disk.

    Convention: Forward rotation is clockwise, matching the paper's convention.
    This uses ζ₅⁴ = exp(-2πi/5) for the rotation factor. -/
noncomputable def genA (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ leftDisk r then rotateAboutC leftCenter (-2 * π / 5) z else z

/-- Generator B: rotation by -2π/5 (clockwise) about the right disk center (1).
    Acts as the identity outside the right disk.

    Convention: Forward rotation is clockwise, matching the paper's convention.
    This uses ζ₅⁴ = exp(-2πi/5) for the rotation factor. -/
noncomputable def genB (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ rightDisk r then rotateAboutC rightCenter (-2 * π / 5) z else z

/-! ### Circle-based generator expressions

These lemmas show that genA/genB can be expressed using `rotateAboutCircle` with
`Circle.exp (-2 * π / 5)`. This provides a bridge to the Circle-based rotation
infrastructure and enables use of Circle's group properties.

Note: We use -2π/5 for clockwise rotation. Circle.exp (-2π/5) = ζ₅⁴ = ζ₅⁻¹.
-/

/-- genA expressed using Circle-based rotation (inside left disk). -/
lemma genA_in_disk_eq_rotateAboutCircle (r : ℝ) (z : ℂ) (hz : z ∈ leftDisk r) :
    genA r z = rotateAboutCircle leftCenter (Circle.exp (-2 * π / 5)) z := by
  simp only [genA, hz, ↓reduceIte, rotateAboutCircle_eq_rotateAboutC]

/-- genB expressed using Circle-based rotation (inside right disk). -/
lemma genB_in_disk_eq_rotateAboutCircle (r : ℝ) (z : ℂ) (hz : z ∈ rightDisk r) :
    genB r z = rotateAboutCircle rightCenter (Circle.exp (-2 * π / 5)) z := by
  simp only [genB, hz, ↓reduceIte, rotateAboutCircle_eq_rotateAboutC]

/-- Apply a generator or its inverse to a point in ℂ. -/
noncomputable def applyGen (r : ℝ) (z : ℂ) : Generator → ℂ
  | .A    => genA r z                            -- A
  | .Ainv => genA r (genA r (genA r (genA r z))) -- A^-1 = A^4
  | .B    => genB r z                            -- B
  | .Binv => genB r (genB r (genB r (genB r z))) -- B^-1 = B^4

/-- Apply a word to a point in ℂ. -/
noncomputable def applyWord (r : ℝ) (w : Word) (z : ℂ) : ℂ :=
  w.foldl (applyGen r) z

/-- The orbit of a point under the group action in ℂ. -/
noncomputable def orbit (r : ℝ) (z : ℂ) : Set ℂ :=
  { w | ∃ word : Word, applyWord r word z = w }

end TDCSG.Definitions
