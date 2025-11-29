/-
Copyright (c) 2025 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Real Dynamics Definitions

This file contains core definitions for orbit theory of real-valued functions.

## Main definitions

* `orbitSet`: The orbit set of a point x under iteration of f
* `HasInfiniteOrbit`: A point has infinite orbit if no orbit point is periodic

-/

namespace RealDynamics

open Function Set

/-- The orbit set of a point x under iteration of f. -/
def orbitSet (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ (n : ℕ), (f^[n]) x = y}

/-- A point has infinite orbit if no point in its orbit is periodic.
    This is equivalent to the orbit set being infinite. -/
def HasInfiniteOrbit (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f

end RealDynamics
