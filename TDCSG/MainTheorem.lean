/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.TwoDisk
import TDCSG.Definitions.GroupAction

/-!
# Main Theorem: GG₅ is Infinite at the Critical Radius

Theorem 2 from "Two-Disk Compound Symmetry Groups" (arXiv:2302.12950v1).
-/

open TDCSG.Definitions
-- open TDCSG.CompoundSymmetry.GG5

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


/-- **Theorem 2**: The compound symmetry group GG₅ at the critical radius is infinite. -/
def StatementOfTheorem : Prop :=
  ∃ p, (orbit GG5_critical.r1 p).Infinite
