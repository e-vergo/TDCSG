/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Geometry
import Mathlib.NumberTheory.Real.GoldenRatio

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
- `segmentPoint` : Parametric representation of segment E'E in complex plane
- `segmentPointPlane` : Parametric representation of segment E'E in Plane
- `translation_length_1`, `translation_length_2`, `segment_length` : Segment lengths

## References
- Two-Disk Compound Symmetry Groups, arXiv:2302.12950v1
-/

namespace TDCSG.Definitions

open Complex Real

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

/-! ### Segment Parameterization -/

/-- Parametric representation of segment E'E.
    At t=0, this gives E'; at t=1, this gives E.
    The segment passes through F at t=t_F and G at t=t_G. -/
noncomputable def segmentPoint (t : ℝ) : ℂ := E' + t • (E - E')

/-- Segment parameterization in Plane coordinates. -/
noncomputable def segmentPointPlane (t : ℝ) : Plane :=
  toPlane (segmentPoint t)

/-! ### Translation and Segment Lengths -/

/-- The translation length |F - (-F)| = 2|F|.
    This is the length of translation by word w1 in the IET. -/
noncomputable def translation_length_1 : ℝ := ‖F - (-F)‖

/-- The translation length |E - G|.
    This is the length of translation by word w2 in the IET. -/
noncomputable def translation_length_2 : ℝ := ‖E - G‖

/-- The total segment length |E - E'| = 2|E|. -/
noncomputable def segment_length : ℝ := ‖E - E'‖

end TDCSG.Definitions
