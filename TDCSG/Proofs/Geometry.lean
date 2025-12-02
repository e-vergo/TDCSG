/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.IETOrbit
import TDCSG.Proofs.OrbitInfinite
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points

/-!
# Basic Geometry for the GG5 Construction

This file establishes fundamental geometric properties of the critical radius used in the GG5
construction, including its positivity and minimal polynomial.

## Main results

- `r_crit_pos`: The critical radius is positive
- `r_crit_minimal_poly`: The critical radius satisfies r⁴ - 7r² + 11 = 0

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real
open TDCSG.Definitions

lemma r_crit_pos : 0 < r_crit := by
  simp only [r_crit, φ]
  apply Real.sqrt_pos_of_pos
  linarith [Real.goldenRatio_pos]

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
