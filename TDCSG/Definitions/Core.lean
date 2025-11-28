/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Core Definitions for TDCSG

This file contains the fundamental constants and type aliases used throughout the TDCSG project.
All definitions here should be human-reviewable for mathematical correctness.

## Main definitions
- `φ` : The golden ratio (1 + √5)/2
- `r_crit` : The critical radius √(3 + φ)
- `Plane` : The Euclidean plane ℝ²
- `Word` : Group words as lists of generator indices
-/

namespace TDCSG.Definitions

open Real

/-! ### Type Aliases -/

/-- The Euclidean plane ℝ². -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A word in generators A, B and their inverses.
    First component: false = A, true = B.
    Second component: true = generator, false = inverse. -/
abbrev Word := List (Bool × Bool)

/-! ### Core Constants -/

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def φ : ℝ := Real.goldenRatio

/-- The critical radius for GG5: r_crit = √(3 + φ). -/
noncomputable def r_crit : ℝ := Real.sqrt (3 + φ)

end TDCSG.Definitions
