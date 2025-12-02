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

This file specializes the n-fold group theory to the 5-fold case (GG5)
and establishes connections between the general and specialized versions.

## Main definitions

- `genA_perm r`: The 5-fold generator A as a permutation
- `genB_perm r`: The 5-fold generator B as a permutation
- `groupOrbit n hn r z`: The group orbit of z under GG(n,n) at radius r
- `GG5_orbit z`: The orbit of z under GG5 at the critical radius

## Main statements

- `genA_bijective`: The 5-fold generator A is bijective
- `genB_bijective`: The 5-fold generator B is bijective
- `genA_eq_genA_n_5`: Equivalence between 5-fold and n-fold versions
- `TwoDiskCompoundSymmetryGroup_5_eq`: Group equality for n=5 specialization

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

lemma genA_bijective (r : Real) : Function.Bijective (genA r) := by
  have h : genA r = genA_n 5 r := funext (genA_eq_genA_n_5 r)
  rw [h]
  exact genA_n_bijective 5 (by norm_num) r

lemma genB_bijective (r : Real) : Function.Bijective (genB r) := by
  have h : genB r = genB_n 5 r := funext (genB_eq_genB_n_5 r)
  rw [h]
  exact genB_n_bijective 5 (by norm_num) r

noncomputable def genA_perm (r : Real) : Equiv.Perm Complex :=
  Equiv.ofBijective (genA r) (genA_bijective r)

noncomputable def genB_perm (r : Real) : Equiv.Perm Complex :=
  Equiv.ofBijective (genB r) (genB_bijective r)

@[simp]
lemma genA_perm_apply (r : Real) (z : Complex) : genA_perm r z = genA r z := rfl

@[simp]
lemma genB_perm_apply (r : Real) (z : Complex) : genB_perm r z = genB r z := rfl

noncomputable def groupOrbit (n : Nat) (hn : n >= 1) (r : Real) (z : Complex) : Set Complex :=
  MulAction.orbit (TwoDiskCompoundSymmetryGroup n hn r) z

noncomputable def GG5_orbit (z : Complex) : Set Complex :=
  MulAction.orbit GG5_At_Critical_radius z

private lemma genA_n_perm_5_eq_genA_perm (r : Real) :
    (genA_n_perm 5 (by norm_num) r : Equiv.Perm Complex) = genA_perm r := by
  ext z
  exact genA_eq_genA_n_5 r z

private lemma genB_n_perm_5_eq_genB_perm (r : Real) :
    (genB_n_perm 5 (by norm_num) r : Equiv.Perm Complex) = genB_perm r := by
  ext z
  exact genB_eq_genB_n_5 r z

lemma TwoDiskCompoundSymmetryGroup_5_eq (r : Real) :
    TwoDiskCompoundSymmetryGroup 5 (by norm_num) r =
    Subgroup.closure {genA_perm r, genB_perm r} := by
  unfold TwoDiskCompoundSymmetryGroup
  simp only [genA_n_perm_5_eq_genA_perm, genB_n_perm_5_eq_genB_perm]

end TDCSG.Definitions
