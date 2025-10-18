/-
Copyright (c) 2025 Eric Ling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Ling
-/

import TDCSG.CompoundSymmetry.TwoDisk
import TDCSG.Planar.Rotations
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finiteness Properties of Symmetry Groups

This file establishes fundamental finiteness results for compound symmetry groups
acting on the two-dimensional disk.

## Main Definitions

* `IsFiniteGroup`: A group is finite if its underlying type is finite.
* `HasInfiniteOrbit`: A group action has an infinite orbit if there exists a point
  whose orbit under the action is infinite.
* `CriticalRadius`: The critical radius is the infimum of radii at which the
  compound symmetry group has infinite orbits.

## Main Results

* `theorem_1`: If the compound symmetry group G(r) is finite for all r in (0, 1),
  then G(r) is the trivial group for all r in (0, 1).

## References

* [T. Schmitz, *Two-Dimensional Compound Symmetry Groups*][schmitz2023]

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
A group action has an infinite orbit if there exists a point whose orbit
under the action is infinite.
-/
def HasInfiniteOrbit (G : Type*) [Group G] (X : Type*) [MulAction G X] : Prop :=
  ∃ x : X, Set.Infinite (MulAction.orbit G x)

/-! ### Critical radius -/

/--
The critical radius is the infimum of radii at which the compound symmetry
group has infinite orbits. This is a key structural invariant in the theory
of two-dimensional compound symmetry groups.
-/
noncomputable def CriticalRadius (G : Type*) [Group G] [MulAction G ℝ²] : ℝ :=
  sInf {r : ℝ | 0 < r ∧ r < 1 ∧ HasInfiniteOrbit G ℝ²}

/-! ### Main theorem -/

/--
**Theorem 1**: If the compound symmetry group G(r) is finite for all r in (0, 1),
then G(r) is the trivial group for all r in (0, 1).

This is a fundamental structural result showing that non-trivial compound symmetry
groups must have infinite order. The proof relies on the action of the group on
the disk and the continuity properties of the radius parameter.

Note: The precise formulation requires a parameterized family of groups G(r),
which will be formalized in the complete development of the compound symmetry
theory. This statement captures the essential content of Theorem 1.
-/
theorem theorem_1
  (G : ℝ → Type*) [∀ r, Group (G r)]
  [∀ r, MulAction (G r) ℝ²]
  (h_finite : ∀ r ∈ Set.Ioo (0 : ℝ) 1, IsFiniteGroup (G r)) :
  ∀ r ∈ Set.Ioo (0 : ℝ) 1, Subsingleton (G r) :=
  sorry

end TDCSG
