import Mathlib.Dynamics.PeriodicPts.Defs
import TDCSG.Definitions.IET

namespace RealDynamics

open Function Set

def orbitSet (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {y | ∃ (n : ℕ), (f^[n]) x = y}

def HasInfiniteOrbit (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y ∈ orbitSet f x, y ∉ Function.periodicPts f

end RealDynamics

namespace TDCSG.Definitions

open RealDynamics

noncomputable def GG5_displacement (x : ℝ) : ℝ :=
  if x < length1 then displacement0
  else if x < length1 + length2 then displacement1
  else displacement2

noncomputable def cumulative_displacement (y : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, GG5_displacement ((GG5_induced_IET.toFun^[k]) y)

end TDCSG.Definitions
