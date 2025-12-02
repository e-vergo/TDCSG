/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Geometry
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Special Points

This file defines the special points in the two-disk system that are critical
for establishing the interval exchange transformation.

## Main definitions

- `E`, `E'`: The endpoints of the critical segment on the boundary
- `F`: A special point related to the first generator action
- `G`: A special point related to the second generator action
- `psi`: The golden conjugate $-φ^{-1}$
- `t_F`, `t_G`: Parameter values for points F and G on the segment
- `segmentPoint t`: Parameterization of the segment from E' to E
- `translation_length_1`, `translation_length_2`: Displacement lengths for the IET
- `segment_length`: Length of the segment E'E

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open Complex Real

/-- The point E = ζ₅⁴ - ζ₅³ on the boundary of the disk intersection. -/
noncomputable def E : ℂ := ζ₅^4 - ζ₅^3

/-- The point E' = -E, the opposite endpoint of the critical segment. -/
noncomputable def E' : ℂ := -E

/-- The point F = 1 - ζ₅⁴ + ζ₅³ - ζ₅², image of E under generator A. -/
noncomputable def F : ℂ := 1 - ζ₅^4 + ζ₅^3 - ζ₅^2

/-- The point G = 2F - E, image of E under generator B. -/
noncomputable def G : ℂ := 2 * F - E

/-- The golden conjugate ψ = -φ⁻¹ = -(√5 - 1)/2. -/
noncomputable abbrev psi : ℝ := -Real.goldenConj

/-- Parameter t for point F on the segment E'E. -/
noncomputable def t_F : ℝ := (1 + Real.sqrt 5) / 4

/-- Parameter t for point G on the segment E'E. -/
noncomputable abbrev t_G : ℝ := psi

/-- Parameterization of the segment from E' to E by parameter t ∈ [0,1]. -/
noncomputable def segmentPoint (t : ℝ) : ℂ := E' + t • (E - E')

/-- Length of the first translation interval in the IET. -/
noncomputable def translation_length_1 : ℝ := ‖F - (-F)‖

/-- Length of the second translation interval in the IET. -/
noncomputable def translation_length_2 : ℝ := ‖E - G‖

/-- Total length of the segment from E' to E. -/
noncomputable def segment_length : ℝ := ‖E - E'‖

end TDCSG.Definitions
