/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import TDCSG.Definitions.Geometry

/-!
# Statement of Main Theorem

This file contains the complete statement of Theorem 2 from "Two-Disk Compound Symmetry Groups"
(arXiv:2302.12950v1): **GG5 is infinite at the critical radius**.

All definitions needed to understand the theorem are imported from the Definitions modules.
The proof is in `ProofOfMainTheorem.lean`.

## Mathematical Background

A two-disk compound symmetry group GG(n,m) consists of:
- Two overlapping closed disks in the plane
- Generator `a`: rotation by 2π/n about the left disk center
- Generator `b`: rotation by 2π/m about the right disk center

The group GG5 = GG(5,5) uses 5-fold rotations on both disks.

The critical radius r_crit = √(3 + φ) (where φ is the golden ratio) is the exact value
where the group transitions from finite to infinite.

## Main definitions (from TDCSG.Definitions)

* `Plane` : The Euclidean plane ℝ²
* `φ` : The golden ratio (1 + √5)/2
* `r_crit` : The critical radius √(3 + φ)
* `leftCenter`, `rightCenter` : Centers of the two disks at (-1, 0) and (1, 0)
* `leftDisk`, `rightDisk` : The closed disks of radius r centered at ±1
* `rotateAround` : Rotation about a point by an angle
* `genA`, `genB` : The two generators (5-fold rotations)
* `orbit` : The orbit of a point under the group action
* `StatementOfTheorem` : GG5 is infinite at the critical radius

## References

* Two-Disk Compound Symmetry Groups, Hearn, Kretschmer, Rokicki, Streeter, Vergo,
  arXiv:2302.12950v1
-/

open Real Classical TDCSG.Definitions

/-- Generator A: rotation by 2π/5 about the left disk center.
    Acts as the identity outside the left disk. -/
noncomputable def genA (r : ℝ) (p : Plane) : Plane :=
  if p ∈ leftDisk r then rotateAround leftCenter (2 * π / 5) p else p

/-- Generator B: rotation by 2π/5 about the right disk center.
    Acts as the identity outside the right disk. -/
noncomputable def genB (r : ℝ) (p : Plane) : Plane :=
  if p ∈ rightDisk r then rotateAround rightCenter (2 * π / 5) p else p

/-! ### Group Action and Orbits -/

-- Word is now imported from TDCSG.Definitions.Core

/-- Apply a generator or its inverse to a point. -/
noncomputable def applyGen (r : ℝ) (p : Plane) (g : Bool × Bool) : Plane :=
  match g with
  | (false, true)  => genA r p                            -- A
  | (false, false) => genA r (genA r (genA r (genA r p))) -- A⁻¹ = A⁴
  | (true, true)   => genB r p                            -- B
  | (true, false)  => genB r (genB r (genB r (genB r p))) -- B⁻¹ = B⁴

/-- Apply a word to a point. -/
noncomputable def applyWord (r : ℝ) (w : Word) (p : Plane) : Plane :=
  w.foldl (applyGen r) p

/-- The orbit of a point under the group action. -/
noncomputable def orbit (r : ℝ) (p : Plane) : Set Plane :=
  { q | ∃ w : Word, applyWord r w p = q }

/-! ### Main Theorem Statement -/

/-- **Theorem 2 (Hearn et al.)**: GG5 is infinite at the critical radius.

At radius r_crit = √(3 + φ), where φ = (1 + √5)/2 is the golden ratio, the two-disk
compound symmetry group GG(5,5) is infinite.

The proof shows that segment E'E (where E = ζ₅ - ζ₅² for ζ₅ = e^(2πi/5)) admits an
interval exchange transformation induced by three specific group words. The translation
lengths are in golden ratio proportion, making the IET aperiodic and yielding infinite
orbits.

This is the exact transition point: for r < r_crit, the group is finite;
for r ≥ r_crit, the group is infinite. -/
def StatementOfTheorem : Prop :=
  ∃ (p : Plane), (orbit r_crit p).Infinite
