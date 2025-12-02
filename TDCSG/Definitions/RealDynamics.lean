/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Dynamics.PeriodicPts.Defs
import TDCSG.Definitions.IET

/-!
# Real Dynamics

This file defines real-valued dynamical systems concepts used to analyze the
interval exchange transformation, particularly orbit structure and displacement functions.

## Main definitions

- `orbitSet f x`: The orbit of x under repeated application of f : ℝ → ℝ
- `HasInfiniteOrbit f x`: Property that x has no periodic points in its orbit
- `GG5_displacement x`: The displacement function for the GG5 IET
- `cumulative_displacement y n`: Sum of displacements over n iterations

## Implementation notes

The displacement function maps points in [0,1] to their translation amounts,
which depend on which of the three intervals they lie in.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace RealDynamics

open Function Set

/-- The orbit of x under repeated application of f. -/
def orbitSet (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ (n : ℕ), (f^[n]) x = y}

/-- A point has infinite orbit if no point in its orbit is periodic. -/
def HasInfiniteOrbit (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f

end RealDynamics

namespace TDCSG.Definitions

open RealDynamics

/-- The displacement function for GG5, assigning translation amounts to each interval. -/
noncomputable def GG5_displacement (x : ℝ) : ℝ :=
  if x < length1 then displacement0
  else if x < length1 + length2 then displacement1
  else displacement2

/-- Cumulative displacement after n iterations of the IET. -/
noncomputable def cumulative_displacement (y : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, GG5_displacement ((GG5_induced_IET.toFun^[k]) y)

end TDCSG.Definitions
