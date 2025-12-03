/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Geometry
import TDCSG.Definitions.GroupAction
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Main Theorem Statement

This file contains the statement of the main theorem from arXiv:2302.12950v1:
the compound symmetry group GG(5,5) at the critical radius is infinite.

## Main definitions

- `GG5_At_Critical_radius`: The group GG(5,5) at the critical radius r_crit = √(3 + φ)
- `StatementOfTheorem`: The proposition that GG5_At_Critical_radius is infinite

The underlying group structure definitions (`genA_n_perm`, `genB_n_perm`,
`TwoDiskCompoundSymmetryGroup`) are imported from Definitions.GroupAction.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

open Real Complex
open scoped Circle
open TDCSG.Definitions (leftDisk rightDisk leftCenter rightCenter rotateAboutC
  genA_n genB_n genA_n_bijective genB_n_bijective genA_n_perm genB_n_perm
  TwoDiskCompoundSymmetryGroup r_crit φ)

/-- The compound symmetry group GG(5,5) at the critical radius r_crit = √(3 + φ),
where φ = (1 + √5)/2 is the golden ratio.

This is the central object of study in the main theorem. At this specific radius,
the group transitions from finite to infinite due to the golden ratio relationship
between the disk overlap and rotation angles. -/
noncomputable def GG5_At_Critical_radius : Subgroup (Equiv.Perm ℂ) :=
  TwoDiskCompoundSymmetryGroup 5 (by norm_num) r_crit

/-- **Main Theorem**: The compound symmetry group GG(5,5) at the critical radius is infinite.

This is the central result from arXiv:2302.12950v1 "Two-Disk Compound Symmetry Groups"
(Hearn, Kretschmer, Rokicki, Streeter, Vergo).

## Mathematical Statement

The two-disk compound symmetry group GG_5(r) with n = 5 (pentagonal rotations) becomes
infinite precisely at the critical radius r_crit = √(3 + φ) ≈ 2.149, where φ = (1 + √5)/2
is the golden ratio.

## Proof Strategy (from paper)

The proof works in the complex plane, interpreting the plane as ℂ with disks centered at
-1 and 1. Let ζ₅ = e^(2πi/5), and define key points:
- E = ζ₅ - ζ₅² (with |E + 1| = r_crit)
- F = 1 - ζ₅ + ζ₅² - ζ₅³ (lies on segment E'E)
- G = 2F - E (also on segment E'E)

Three specific move sequences act as translations on the line segment E'E:
1. a⁻²b⁻¹a⁻¹b⁻¹ maps E'F' to GF
2. ab ab² maps F'G' to FE
3. ab ab⁻¹a⁻¹b⁻¹ maps G'E to E'G

Since |E - E'|/|F - F'| = φ (the golden ratio), these translations have irrational
ratio to the segment length. Iterating these piecewise translations produces an
infinite orbit for the origin, hence the group is infinite.

## References

* arXiv:2302.12950v1, Section "Geometric Constructions", Theorem on page 5
* The proof demonstrates a connection between golden ratio geometry and group infinitude
-/
def StatementOfTheorem : Prop :=
  Infinite GG5_At_Critical_radius
