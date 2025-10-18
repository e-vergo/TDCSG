/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.CompoundSymmetry.GG5.IET
import TDCSG.CompoundSymmetry.Finiteness
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Critical Radius for the GG(5,5) Compound Symmetry System

This file defines the critical radius for the compound symmetry system
GG(5,5) and establishes its basic properties.

## Main definitions

- `r_crit`: The critical radius √(3 + φ) where φ is the golden ratio

## Main results

- `critical_radius_pos`: The critical radius is positive
- `golden_ratio_sq`: The golden ratio satisfies φ² = φ + 1
- `critical_radius_polynomial`: r_crit² - φ = 3

## References

* [Richard Kenyon, *Tiling a polygon with parallelograms*][Kenyon1993]
* [Richard Kenyon, *The Golden Ratio and Compound Symmetries*][Kenyon2023]

## Tags

compound symmetry, critical radius, golden ratio
-/

namespace CompoundSymmetry.GG5

open CompoundSymmetry Real

/-- Notation for the golden ratio φ = (1 + √5)/2. -/
local notation "φ" => Real.goldenRatio

/-- The critical radius value for GG(5,5). -/
noncomputable def r_crit : ℝ := Real.sqrt (3 + φ)

/-- The critical radius is positive. -/
theorem critical_radius_pos : 0 < r_crit := by
  unfold r_crit
  apply Real.sqrt_pos.mpr
  linarith [Real.goldenRatio_pos]

/-- The golden ratio satisfies φ² = φ + 1. -/
theorem golden_ratio_sq : φ^2 = φ + 1 := Real.goldenRatio_sq

/-- The critical radius satisfies r_crit² - φ = 3. -/
theorem critical_radius_polynomial : r_crit^2 - φ = 3 := by
  unfold r_crit
  rw [Real.sq_sqrt]
  · ring
  · linarith [Real.goldenRatio_pos]

end CompoundSymmetry.GG5
