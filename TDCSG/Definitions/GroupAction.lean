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
-/

namespace TDCSG.Definitions

open Real

/-- Generator A: rotation by 2 pi/5 about the left disk center.
    Acts as the identity outside the left disk. -/
noncomputable def genA (r : Real) (p : Plane) : Plane := by
  classical
  exact if p ∈ leftDisk r then rotateAroundPoint leftCenter (2 * π / 5) p else p

/-- Generator B: rotation by 2 pi/5 about the right disk center.
    Acts as the identity outside the right disk. -/
noncomputable def genB (r : Real) (p : Plane) : Plane := by
  classical
  exact if p ∈ rightDisk r then rotateAroundPoint rightCenter (2 * π / 5) p else p

/-- Apply a generator or its inverse to a point. -/
noncomputable def applyGen (r : Real) (p : Plane) (g : Bool × Bool) : Plane :=
  match g with
  | (false, true)  => genA r p                            -- A
  | (false, false) => genA r (genA r (genA r (genA r p))) -- A^-1 = A^4
  | (true, true)   => genB r p                            -- B
  | (true, false)  => genB r (genB r (genB r (genB r p))) -- B^-1 = B^4

/-- Apply a word to a point. -/
noncomputable def applyWord (r : Real) (w : Word) (p : Plane) : Plane :=
  w.foldl (applyGen r) p

/-- The orbit of a point under the group action. -/
noncomputable def orbit (r : Real) (p : Plane) : Set Plane :=
  { q | ∃ w : Word, applyWord r w p = q }

end TDCSG.Definitions
