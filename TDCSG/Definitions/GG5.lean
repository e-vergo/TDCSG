/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.TwoDisk

/-!
# GG5 System Definition

This file contains the definition of the GG5 two-disk system at the critical radius.

## Main definitions
- `GG5_critical` : The TwoDiskSystem at the critical radius r_crit = sqrt(3 + phi)
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions

/-- The GG5 two-disk system at the critical radius. -/
noncomputable def GG5_critical :
    CompoundSymmetry.TwoDiskSystem where
  r1 := r_crit
  r2 := r_crit
  n1 := 5
  n2 := 5
  r1_pos := by
    unfold r_crit φ
    apply Real.sqrt_pos_of_pos
    linarith [Real.goldenRatio_pos]
  r2_pos := by
    unfold r_crit φ
    apply Real.sqrt_pos_of_pos
    linarith [Real.goldenRatio_pos]
  n1_ge := by norm_num
  n2_ge := by norm_num

end TDCSG.CompoundSymmetry.GG5
