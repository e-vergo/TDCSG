/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.PermutationGroup
import TDCSG.Proofs.IETOrbit
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finite.Defs

/-!
# Group Theory for the GG5 Compound Symmetry Group

This file establishes the equivalence between word orbits and group-theoretic orbits
for the two-disk compound symmetry group.

## Main results

- `orbit_eq_MulAction_orbit`: Word orbits coincide with group-theoretic orbits
- `infinite_orbit_implies_infinite_group`: An infinite orbit implies the group is infinite

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions
open scoped Complex

lemma word_orbit_subset_group_orbit (r : Real) (z : Complex) :
    orbit r z ⊆ MulAction.orbit (TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) z := by
  intro w hw
  obtain ⟨word, hw_eq⟩ := hw
  rw [MulAction.mem_orbit_iff]
  use wordToPerm r word
  rw [<- hw_eq]
  exact wordToPerm_action r word z

lemma group_orbit_subset_word_orbit (r : Real) (z : Complex) :
    MulAction.orbit (TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) z ⊆ orbit r z := by
  intro w hw
  rw [MulAction.mem_orbit_iff] at hw
  obtain ⟨g, hgw⟩ := hw

  obtain ⟨word, hword⟩ := closure_element_has_word r g

  use word
  rw [<- hgw]

  have h2 : (wordToPerm r word).val z = applyWord r word z := wordToPerm_action r word z
  calc applyWord r word z
      = (wordToPerm r word).val z := h2.symm
    _ = g.val z := by rw [<- hword]
    _ = g • z := rfl

theorem orbit_eq_MulAction_orbit (r : Real) (z : Complex) :
    orbit r z = MulAction.orbit (TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) z := by
  apply Set.eq_of_subset_of_subset
  . exact word_orbit_subset_group_orbit r z
  . exact group_orbit_subset_word_orbit r z

lemma infinite_orbit_implies_infinite_group {G : Type*} [Group G] [MulAction G Complex]
    (z : Complex) (h : (MulAction.orbit G z).Infinite) : Infinite G := by
  by_contra hfin
  push_neg at hfin
  haveI : Finite G := hfin
  exact h (Finite.finite_mulAction_orbit z)

end TDCSG.CompoundSymmetry.GG5
