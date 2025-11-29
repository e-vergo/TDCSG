/-
Copyright (c) 2025 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Proofs.IET
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Orbit Definitions

This file contains core definitions for orbit theory of real-valued functions.

## Main definitions

* `orbitSet`: The orbit set of a point x under iteration of f
* `HasInfiniteOrbit`: A point has infinite orbit if no orbit point is periodic
* `GG5_displacement`: The displacement function for the GG5 IET
* `cumulative_displacement`: The cumulative displacement over n iterates

-/

namespace Orbit

open Function Set

/-- The orbit set of a point x under iteration of f. -/
def orbitSet (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ (n : ℕ), (f^[n]) x = y}

/-- A point has infinite orbit if no point in its orbit is periodic.
    This is equivalent to the orbit set being infinite. -/
def HasInfiniteOrbit (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f

end Orbit

namespace CompoundSymmetry.GG5

open PiecewiseIsometry Real Function Set Orbit TDCSG.Definitions

/-- The displacement function for the GG5 IET: f(x) - x for x in [0,1).
    Takes value d_i when x is in interval i. -/
noncomputable def GG5_displacement (x : ℝ) : ℝ :=
  if x < length1 then displacement0
  else if x < length1 + length2 then displacement1
  else displacement2

/-- The cumulative displacement over n iterates starting from y. -/
noncomputable def cumulative_displacement (y : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, GG5_displacement ((GG5_induced_IET.toFun^[k]) y)

end CompoundSymmetry.GG5
