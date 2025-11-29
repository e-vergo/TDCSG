/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.WordCorrespondence
import TDCSG.Proofs.OrbitInfinite
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points

/-!
# GG5 Geometry Module

This module re-exports from the split modules and contains the main theorem infrastructure.

The GG5 geometric construction has been refactored into:
- `Points.lean`: Key geometric points E, E', F, G, segment parameterization
- `SegmentGeometry.lean`: Translation lengths, segment ratios, irrationality, disk intersection, rotation correspondence
- `WordCorrespondence.lean`: Group words for IET intervals, orbit correspondence

## Main Definitions

- `GG5_critical`: The TwoDiskSystem at the critical radius

## Main Results

- `r_crit_minimal_poly`: The critical radius satisfies x^4 - 7x^2 + 11 = 0
- `GG5_infinite_at_critical_radius`: GG5 is infinite at r = sqrt(3 + phi)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-! ### Basic lemmas -/

/-- The critical radius is positive. -/
lemma r_crit_pos : 0 < r_crit := by
  unfold r_crit φ
  apply Real.sqrt_pos_of_pos
  linarith [Real.goldenRatio_pos]

/-! ### Main Results -/

/-- The critical radius satisfies x^4 - 7x^2 + 11 = 0. -/
lemma r_crit_minimal_poly :
    r_crit ^ 4 - 7 * r_crit ^ 2 + 11 = 0 := by
  unfold r_crit
  have h1 : (Real.sqrt (3 + Real.goldenRatio)) ^ 2 =
      3 + Real.goldenRatio := by
    rw [sq_sqrt]
    linarith [Real.goldenRatio_pos]
  have h2 : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    Real.goldenRatio_sq
  calc (Real.sqrt (3 + Real.goldenRatio)) ^ 4 -
          7 * (Real.sqrt (3 + Real.goldenRatio)) ^ 2 + 11
      = ((Real.sqrt (3 + Real.goldenRatio)) ^ 2) ^ 2 -
          7 * (Real.sqrt (3 + Real.goldenRatio)) ^ 2 +
          11 := by
        ring
    _ = (3 + Real.goldenRatio) ^ 2 -
          7 * (3 + Real.goldenRatio) + 11 := by
        rw [h1]
    _ = 9 + 6 * Real.goldenRatio + Real.goldenRatio ^ 2 -
          21 - 7 * Real.goldenRatio + 11 := by
        ring
    _ = 9 + 6 * Real.goldenRatio +
          (Real.goldenRatio + 1) - 21 -
          7 * Real.goldenRatio + 11 := by
        rw [h2]
    _ = 0 := by ring

end TDCSG.CompoundSymmetry.GG5
