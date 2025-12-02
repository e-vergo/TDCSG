/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.MainTheorem
import TDCSG.Definitions.GroupAction
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Group Theory Specialization

This file defines the group orbit for the two-disk compound symmetry group.

## Main definitions

- `groupOrbit n hn r z`: The group orbit of z under GG(n,n) at radius r

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open scoped Complex

open _root_ (φ r_crit genA_n genB_n genA_n_bijective genB_n_bijective genA_n_perm genB_n_perm TwoDiskCompoundSymmetryGroup GG5_At_Critical_radius)

lemma genA_eq_genA_n_5 (r : Real) (z : Complex) : genA r z = genA_n 5 r z := by
  unfold genA genA_n
  simp only [Nat.cast_ofNat]

lemma genB_eq_genB_n_5 (r : Real) (z : Complex) : genB r z = genB_n 5 r z := by
  unfold genB genB_n
  simp only [Nat.cast_ofNat]

noncomputable def groupOrbit (n : Nat) (hn : n >= 1) (r : Real) (z : Complex) : Set Complex :=
  MulAction.orbit (TwoDiskCompoundSymmetryGroup n hn r) z

end TDCSG.Definitions
