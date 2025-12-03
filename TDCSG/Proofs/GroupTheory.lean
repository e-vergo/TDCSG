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

/-- The word-based orbit of a point is contained in its group-theoretic orbit.

Every element of the word orbit arises from applying some finite sequence of generators,
which corresponds to an element of the compound symmetry group acting on the point. -/
lemma word_orbit_subset_group_orbit (r : Real) (z : Complex) :
    orbit r z ⊆ MulAction.orbit (TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) z := by
  intro w hw
  obtain ⟨word, hw_eq⟩ := hw
  rw [MulAction.mem_orbit_iff]
  use wordToPerm r word
  rw [<- hw_eq]
  exact wordToPerm_action r word z

/-- The group-theoretic orbit of a point is contained in its word-based orbit.

Every group element in the closure of the generators can be expressed as a finite word,
so every point in the group orbit is reachable by some word. This uses the key fact
that closure elements have word representations (`closure_element_has_word`). -/
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

/-- **Main result**: Word orbits and group-theoretic orbits coincide for `GG_5(r)`.

This theorem establishes that the computational notion of orbit (points reachable by
finite words in the generators `a`, `b`) is exactly the group-theoretic orbit under
the `MulAction` of the two-disk compound symmetry group. This equivalence is essential
for transferring results between the combinatorial word-based approach and the
algebraic group action framework.

In the paper, the group `GG_{n_1,n_2}(r_1,r_2)` is defined by generators performing
rotations of overlapping disks. This theorem justifies using word-based orbit
computations to draw conclusions about the group structure. -/
theorem orbit_eq_MulAction_orbit (r : Real) (z : Complex) :
    orbit r z = MulAction.orbit (TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) z := by
  apply Set.eq_of_subset_of_subset
  . exact word_orbit_subset_group_orbit r z
  . exact group_orbit_subset_word_orbit r z

/-- An infinite orbit implies the group itself is infinite.

This is the contrapositive of the fact that finite groups have finite orbits.
The proof proceeds by contradiction: if the group were finite, then by
`Finite.finite_mulAction_orbit`, the orbit would also be finite, contradicting
the hypothesis.

This result is key to the paper's approach: by exhibiting a point with an
infinite orbit (established via the IET correspondence at the critical radius),
we conclude that `GG_5(r_crit)` is an infinite group. This relates to Theorem 1
in the paper, which characterizes which `GG_{n_1,n_2}` families have infinite
members based on whether `lcm(n_1, n_2) ∉ {2, 3, 4, 6}`. -/
lemma infinite_orbit_implies_infinite_group {G : Type*} [Group G] [MulAction G Complex]
    (z : Complex) (h : (MulAction.orbit G z).Infinite) : Infinite G := by
  by_contra hfin
  push_neg at hfin
  haveI : Finite G := hfin
  exact h (Finite.finite_mulAction_orbit z)

end TDCSG.CompoundSymmetry.GG5
