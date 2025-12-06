/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.GG10.Core
import TDCSG.GG10.OrbitInfinite
import TDCSG.Definitions.Geometry
import TDCSG.Definitions.GroupAction
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Main Theorem Statement for GG(10,10)

This file contains the statement of the main theorem for GG(10,10):
the compound symmetry group GG(10,10) at the critical radius is infinite.

## Main definitions

- `GG10_At_Critical_radius`: The group GG(10,10) at the critical radius r_crit_10 = √(4 - φ)
- `StatementOfTheorem_GG10`: The proposition that GG10_At_Critical_radius is infinite

## Key difference from GG5

Unlike GG5 which has critical radius √(3 + φ) ≈ 2.149, GG10 has critical radius
√(4 - φ) ≈ 1.543. The 10-fold rotation symmetry leads to a 2-interval IET (instead
of GG5's 3-interval) that is conjugate to irrational rotation by 1/φ on the circle.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.GG10

open Real Complex
open scoped Circle
open TDCSG.Definitions (leftDisk rightDisk leftCenter rightCenter rotateAboutC
  genA_n genB_n genA_n_bijective genB_n_bijective genA_n_perm genB_n_perm
  TwoDiskCompoundSymmetryGroup φ)

/-- The compound symmetry group GG(10,10) at the critical radius r_crit_10 = √(4 - φ),
where φ = (1 + √5)/2 is the golden ratio.

At this radius, the group becomes infinite due to the golden ratio relationship
in the induced 2-interval exchange transformation. -/
noncomputable def GG10_At_Critical_radius : Subgroup (Equiv.Perm ℂ) :=
  TwoDiskCompoundSymmetryGroup 10 (by norm_num) r_crit_10

/-- **Main Theorem for GG10**: The compound symmetry group GG(10,10) at the critical
radius is infinite.

## Mathematical Statement

The two-disk compound symmetry group GG_10(r) with n = 10 (decagonal rotations) becomes
infinite at the critical radius r_crit_10 = √(4 - φ) ≈ 1.543, where φ = (1 + √5)/2
is the golden ratio.

## Proof Strategy

The proof works via a 2-interval exchange transformation on the segment E'₁₀E₁₀:
- E₁₀ = ζ₁₀ - ζ₁₀² where ζ₁₀ = e^(2πi/10)
- E'₁₀ = -E₁₀

The 2-interval IET has intervals [0, 1/φ) and [1/φ, 1) with:
- Displacement +（2-φ) on the first interval (via word w₁ = a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³)
- Displacement -1/φ on the second interval (via word w₂ = a⁻¹b⁻¹ab)

Since the rotation number 1/φ is irrational, the IET has no periodic orbits,
implying the group is infinite.

## Comparison with GG5

- GG5: 3-interval IET with cyclic permutation, critical radius √(3 + φ) ≈ 2.149
- GG10: 2-interval IET with swap permutation, critical radius √(4 - φ) ≈ 1.543

The GG10 case is technically simpler because 2-interval IETs are conjugate to
rotations, and irrationality of the rotation angle directly implies minimality.

## References

* arXiv:2302.12950v1
-/
def StatementOfTheorem_GG10 : Prop :=
  Infinite GG10_At_Critical_radius

end TDCSG.GG10
