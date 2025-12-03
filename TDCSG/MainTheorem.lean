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

/-- **Main Theorem**: The compound symmetry group GG₅ at the critical radius is infinite.

This formalizes Theorem 2 from arXiv:2302.12950v1, showing that the two-disk
compound symmetry group with 5-fold rotations exhibits a phase transition at
r_crit = √(3 + φ), where the group becomes infinite. -/
def StatementOfTheorem : Prop :=
  Infinite GG5_At_Critical_radius
