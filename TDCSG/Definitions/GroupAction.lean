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

/-- Generator A: rotation by 2π/5 about the left disk center (-1).
    Acts as the identity outside the left disk. -/
noncomputable def genA (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ leftDisk r then rotateAboutC leftCenter (2 * π / 5) z else z

/-- Generator B: rotation by 2π/5 about the right disk center (1).
    Acts as the identity outside the right disk. -/
noncomputable def genB (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ rightDisk r then rotateAboutC rightCenter (2 * π / 5) z else z

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

/-- DEPRECATED: Generator A on Plane. Use genA : ℂ → ℂ instead. -/
noncomputable def genAPlane (r : ℝ) (p : Plane) : Plane := by
  classical
  exact if p ∈ leftDiskPlane r then rotateAroundPoint leftCenterPlane (2 * π / 5) p else p

/-- DEPRECATED: Generator B on Plane. Use genB : ℂ → ℂ instead. -/
noncomputable def genBPlane (r : ℝ) (p : Plane) : Plane := by
  classical
  exact if p ∈ rightDiskPlane r then rotateAroundPoint rightCenterPlane (2 * π / 5) p else p

end TDCSG.Definitions
