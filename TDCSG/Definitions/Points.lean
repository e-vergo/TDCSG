/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.Zeta5

/-!
# Geometric Points for GG5

This file defines the key geometric points E, E', F, G on segment E'E
that are critical for the interval exchange transformation analysis.

## Main definitions
- `E` : ζ₅⁴ - ζ₅³ - key point in complex plane (clockwise rotation convention)
- `E'` : -E - reflection of E
- `F`, `G` : Points on segment E'E
- `psi` : Positive golden conjugate = -Real.goldenConj
- `t_F`, `t_G` : Parametric coordinates (t_G = psi)

## References
- Two-Disk Compound Symmetry Groups, arXiv:2302.12950v1
-/

namespace TDCSG.Definitions

open Complex Real
open TDCSG.CompoundSymmetry.GG5

/-! ### Key Geometric Points -/

/-- Point E: E = ζ₅⁴ - ζ₅³ = ζ₅⁻¹ - ζ₅⁻².
    This is the segment direction compatible with CLOCKWISE rotation convention.
    CRITICAL: Per the paper (Theorem 2, page 4), |E + 1| = r_crit,
    meaning E lies on the LEFT disk boundary, not the right!

    Note: This equals conj(ζ₅ - ζ₅²), the conjugate of the counterclockwise convention. -/
noncomputable def E : ℂ := ζ₅^4 - ζ₅^3

/-- Point E': the negation of E. -/
noncomputable def E' : ℂ := -E

/-- Point F on segment E'E: F = 1 - ζ₅⁴ + ζ₅³ - ζ₅².
    This is compatible with clockwise rotation convention.
    F = (1/φ) * E where φ is the golden ratio. -/
noncomputable def F : ℂ := 1 - ζ₅^4 + ζ₅^3 - ζ₅^2

/-- Point G on segment E'E: G = 2F - E. -/
noncomputable def G : ℂ := 2 * F - E

/-! ### Parametric Coordinates -/

/-- The positive golden conjugate: ψ = (√5-1)/2 ≈ 0.618.
    This equals -Real.goldenConj since goldenConj = (1-√5)/2. -/
noncomputable abbrev psi : ℝ := -Real.goldenConj

/-- The parameter value for F on segment E'E: t_F = (1 + √5)/4 ≈ 0.809 -/
noncomputable def t_F : ℝ := (1 + Real.sqrt 5) / 4

/-- The parameter value for G on segment E'E: t_G = ψ = (√5-1)/2 ≈ 0.618.
    This equals psi, the positive golden conjugate. -/
noncomputable abbrev t_G : ℝ := psi

end TDCSG.Definitions
