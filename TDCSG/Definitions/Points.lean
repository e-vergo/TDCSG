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
- `t_G`: Parameter value for point G on the segment
- `segmentPoint t`: Parameterization of the segment from E' to E

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open Complex Real

/-- The point E = ζ₅⁴ - ζ₅³ on the boundary of the disk intersection. -/
noncomputable def E : ℂ := ζ₅^4 - ζ₅^3

/-- The point E' = -E, the opposite endpoint of the critical segment. -/
noncomputable def E' : ℂ := -E

/-- Parameterization of the segment from E' to E by parameter t ∈ [0,1]. -/
noncomputable def segmentPoint (t : ℝ) : ℂ := E' + t • (E - E')

end TDCSG.Definitions
