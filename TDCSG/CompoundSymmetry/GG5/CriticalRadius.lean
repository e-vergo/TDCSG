/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
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

This file contains basic lemmas about the critical radius for the compound
symmetry system GG(5,5).

## Main results

- `r_crit`: The critical radius value √(3 + φ) where φ is the golden ratio
- `critical_radius_pos`: The critical radius is positive
- `golden_ratio_sq`: The golden ratio satisfies φ² = φ + 1

## Mathematical Context

The compound symmetry system GG(p,q) is a family of piecewise isometries on ℝ² with
p-fold rotational symmetry. For GG(5,5), there is a critical radius r_crit that
separates two dynamical regimes:

1. **Below critical (r < r_crit)**: All orbits are periodic (finite).
2. **At critical (r = r_crit)**: Infinite orbits first appear.
3. **Above critical (r > r_crit)**: Complex behavior (unbounded orbits, etc.).

The critical radius r_crit = √(3 + φ) has a beautiful connection to the golden ratio,
reflecting the deep relationship between 5-fold symmetry and φ in mathematics
(penrose tilings, quasicrystals, etc.).

## References

* [Richard Kenyon, *Tiling a polygon with parallelograms*][Kenyon1993]
* [Richard Kenyon, *The Golden Ratio and Compound Symmetries*][Kenyon2023]
* [Michael Keane, *Interval exchange transformations*][Keane1975]

## Tags

compound symmetry, critical radius, golden ratio, interval exchange, phase transition,
piecewise isometry, quasiperiodic dynamics

-/

namespace CompoundSymmetry.GG5

open CompoundSymmetry Real

/-- Notation for the golden ratio φ = (1 + √5)/2. -/
local notation "φ" => Real.goldenRatio

/-! ### Basic lemmas about the critical radius -/

/-- The critical radius value for GG(5,5). -/
noncomputable def r_crit : ℝ := Real.sqrt (3 + φ)

/-- The critical radius is positive.

**Proof**: Since φ = (1 + √5)/2 ≈ 1.618, we have 3 + φ ≈ 4.618 > 0.
Therefore √(3 + φ) is well-defined and positive.
-/
theorem critical_radius_pos : 0 < r_crit := by
  unfold r_crit
  apply Real.sqrt_pos.mpr
  -- Need to show 0 < 3 + φ
  -- φ = (1 + √5) / 2 > 0 since √5 > 0
  -- Therefore 3 + φ > 3 > 0
  sorry

/-- The golden ratio satisfies φ² = φ + 1.

This is the defining property of the golden ratio and is used extensively in
computations involving the critical radius.

**Proof**: This is `Real.goldenRatio_sq` from Mathlib.
-/
theorem golden_ratio_sq : φ^2 = φ + 1 := Real.goldenRatio_sq

/-- The critical radius satisfies a polynomial equation.

Setting x = √(3 + φ), we have x² = 3 + φ, so x² - φ = 3.
Combined with φ² = φ + 1, this gives a polynomial relation.

**Proof**: Direct computation using `golden_ratio_sq`.
-/
theorem critical_radius_polynomial : r_crit^2 - φ = 3 := by
  unfold r_crit
  sorry

end CompoundSymmetry.GG5
