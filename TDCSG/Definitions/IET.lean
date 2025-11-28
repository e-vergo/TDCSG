/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Real.Basic

/-!
# IET Interval Lengths and Displacements

This file defines the interval lengths for the 3-interval exchange transformation
induced by GG5, and the displacement amounts for each interval.

The lengths are in golden ratio proportion, making the IET aperiodic.

## Main definitions
- `segmentParam` : The golden ratio, parameterizing the IET structure
- `length1`, `length2`, `length3` : Interval lengths summing to 1
- `displacement0`, `displacement1`, `displacement2` : Translation amounts
-/

namespace TDCSG.Definitions

open Real

/-! ### Segment parameter and interval lengths -/

/-- Segment parameter for the emergent IET. -/
noncomputable def segmentParam : ℝ := goldenRatio

/-- First fundamental length in the emergent 3-interval IET. -/
noncomputable def length1 : ℝ :=
  1 / (1 + goldenRatio + goldenRatio ^ 2)

/-- Second fundamental length in the emergent 3-interval IET. -/
noncomputable def length2 : ℝ :=
  goldenRatio / (1 + goldenRatio + goldenRatio ^ 2)

/-- Third fundamental length in the emergent 3-interval IET. -/
noncomputable def length3 : ℝ :=
  (goldenRatio ^ 2) / (1 + goldenRatio + goldenRatio ^ 2)

/-! ### Displacement definitions -/

/-- Displacement for interval 0: d_0 = 1 - length1.
    This is the amount by which points in interval 0 are translated. -/
noncomputable def displacement0 : ℝ := 1 - length1

/-- Displacement for interval 1: d_1 = length3 - length1.
    This is the amount by which points in interval 1 are translated. -/
noncomputable def displacement1 : ℝ := length3 - length1

/-- Displacement for interval 2: d_2 = -1/2.
    This is the amount by which points in interval 2 are translated. -/
noncomputable def displacement2 : ℝ := -1/2

end TDCSG.Definitions
