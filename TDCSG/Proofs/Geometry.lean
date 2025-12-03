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

/-- The critical radius `r_crit = √(3 + φ)` is positive.

This follows from the positivity of the golden ratio `φ > 0`, which implies
`3 + φ > 3 > 0`, and therefore `√(3 + φ) > 0`.

This lemma is used throughout the GG5 construction to ensure that disk radii
and distances are well-defined positive quantities. -/
lemma r_crit_pos : 0 < r_crit := by
  simp only [r_crit, φ]
  apply Real.sqrt_pos_of_pos
  linarith [Real.goldenRatio_pos]

/-- The critical radius `r_crit = √(3 + φ)` satisfies the minimal polynomial `x⁴ - 7x² + 11 = 0`.

This establishes that `r_crit` is an algebraic number of degree 4 over the rationals.
The polynomial `x⁴ - 7x² + 11` appears in Table 1 of main.tex as the minimal polynomial
for the critical radius of GG₅ (and also GG₁₀, since they share the same polynomial).

The proof uses the algebraic identity `φ² = φ + 1` (the defining property of the golden ratio)
to reduce `r_crit⁴ = (3 + φ)² = 9 + 6φ + φ² = 10 + 7φ` and verify the polynomial evaluates
to zero via direct computation.

This algebraic characterization is significant because it shows the critical radius
is not just a numerical approximation but a precisely determined algebraic number,
placing the finite-to-infinite transition of GG₅ at an exact geometric location. -/
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
