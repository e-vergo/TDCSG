/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclotomic Definitions - 5th Root of Unity

This file defines zeta5 = e^(2 pi i/5), the primitive 5th root of unity.

## Main definitions
- `zeta5` : The primitive 5th root of unity
-/

namespace TDCSG.Definitions

open scoped Complex
open Complex Real

/-! ### 5th Roots of Unity -/

/-- The primitive 5th root of unity: e^(2 pi i/5) -/
noncomputable def zeta5 : Complex := exp (2 * Real.pi * Complex.I / 5)

/-- Unicode alias for the primitive 5th root of unity -/
noncomputable abbrev ζ₅ : Complex := zeta5

end TDCSG.Definitions
