/-
Copyright (c) 2025-10-18 Eric Ling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Ling
-/

import TDCSG.CompoundSymmetry.TwoDisk
import TDCSG.Planar.Rotations
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finiteness Properties of Symmetry Groups

This file establishes fundamental finiteness results for compound
symmetry groups acting on the two-dimensional disk.

## Main Definitions

* `IsFiniteGroup`: A group is finite if its underlying type is
  finite.
* `HasInfiniteOrbit`: A group action has an infinite orbit if there
  exists a point whose orbit under the action is infinite.
* `CriticalRadius`: The critical radius is the infimum of radii at
  which the compound symmetry group has infinite orbits.

## Main Results

* `finite_group_has_finite_orbits`: A finite group acting on ℝ² has
  only finite orbits.
* `finite_group_no_infinite_orbits`: A finite group cannot have
  infinite orbits in its action on ℝ².

## References

* [Two-Disk Compound Symmetry Groups](https://arxiv.org/abs/2302.12950v1)

## Tags

symmetry groups, finiteness, group actions, two-dimensional disk
-/

namespace TDCSG

open CompoundSymmetry Planar

variable {X : Type*} [TopologicalSpace X]

/-! ### Finiteness of groups -/

/--
A group is finite if its underlying type is finite.
-/
def IsFiniteGroup (G : Type*) [Group G] : Prop :=
  Finite G

/-! ### Infinite orbits -/

/--
A group action has an infinite orbit if there exists a point whose
orbit under the action is infinite.
-/
def HasInfiniteOrbit (G : Type*) [Group G] (X : Type*)
    [MulAction G X] : Prop :=
  ∃ x : X, Set.Infinite (MulAction.orbit G x)

/-! ### Critical radius -/

/--
The critical radius is the infimum of radii at which the compound
symmetry group has infinite orbits.
-/
noncomputable def CriticalRadius (G : Type*)
    [Group G] [MulAction G ℝ²] : ℝ :=
  sInf {r : ℝ | 0 < r ∧ r < 1 ∧ HasInfiniteOrbit G ℝ²}

/-! ### Structural lemmas -/

/--
A finite group acting on ℝ² has only finite orbits.
-/
theorem finite_group_has_finite_orbits (G : Type*) [Group G]
    [Finite G] [MulAction G ℝ²] :
    ∀ x : ℝ², Set.Finite (MulAction.orbit G x) := by
  intro x
  exact Finite.finite_mulAction_orbit x

/--
A finite group cannot have infinite orbits in its action on ℝ².
-/
theorem finite_group_no_infinite_orbits (G : Type*) [Group G]
    [Finite G] [MulAction G ℝ²] :
    ¬ HasInfiniteOrbit G ℝ² := by
  intro ⟨x, hinf⟩
  have hfin := finite_group_has_finite_orbits G x
  exact hinf hfin

end TDCSG
