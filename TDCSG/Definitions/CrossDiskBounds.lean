/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cross-Disk Bound Definitions

This file contains the parameter range definitions for cross-disk bounds
used in proving word validity for different IET intervals.

## Main definitions

* `c_lower_word2`: Lower bound for word2 parameter range (1 - √5)/2
* `c_upper_word2`: Upper bound for word2 parameter range 2 - √5
* `c_lower_word3`: Lower bound for word3 parameter range 2 - √5
-/

namespace TDCSG.Definitions

open Real

/-- The lower bound for c in interval 1 (word2): (1 - √5)/2 ≈ -0.618 -/
noncomputable def c_lower_word2 : ℝ := (1 - √5) / 2

/-- The upper bound for c in interval 1 (word2): 2 - √5 ≈ -0.236 -/
noncomputable def c_upper_word2 : ℝ := 2 - √5

/-- The lower bound for c in interval 2 (word3): 2 - √5 ≈ -0.236 -/
noncomputable def c_lower_word3 : ℝ := 2 - √5

end TDCSG.Definitions
