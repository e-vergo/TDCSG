/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.Points
import TDCSG.MainTheorem

/-!
# Coordinate Conversions

This file provides utilities for converting between complex plane coordinates
and the Euclidean plane representation, plus segment parameterization.

## Main definitions
- `toPlane`, `fromPlane` : Convert between complex and Plane (EuclideanSpace)
- `segmentPoint` : Parametric representation of segment E'E in complex plane
- `segmentPointPlane` : Parametric representation of segment E'E in Plane
- `translation_length_1`, `translation_length_2` : Translation lengths for IET
- `segment_length` : Total length of segment E'E

## Coordinate systems

We work with two coordinate representations:
1. Complex plane C - used for algebraic calculations with zeta5
2. Plane (EuclideanSpace R (Fin 2)) - used for disk geometry

The conversions preserve distances and geometric relationships.
-/

namespace TDCSG.Definitions

open Complex Real
open TDCSG.CompoundSymmetry.GG5

/-! ### Basic coordinate conversions -/

/-- Convert a complex number to a Plane point (EuclideanSpace form). -/
noncomputable def toPlane (z : ℂ) : Plane := ![z.re, z.im]

/-- Convert a Plane point to a complex number. -/
noncomputable def fromPlane (p : Plane) : ℂ := ⟨p 0, p 1⟩

/-! ### Segment parameterization -/

/-- Parametric representation of segment E'E.
    At t=0, this gives E'; at t=1, this gives E.
    The segment passes through F at t=t_F and G at t=t_G. -/
noncomputable def segmentPoint (t : ℝ) : ℂ := E' + t • (E - E')

/-- Segment parameterization in Plane coordinates. -/
noncomputable def segmentPointPlane (t : ℝ) : Plane :=
  toPlane (segmentPoint t)

/-! ### Translation and segment lengths -/

/-- The translation length |F - (-F)| = 2|F|.
    This is the length of translation by word w1 in the IET. -/
noncomputable def translation_length_1 : ℝ := ‖F - (-F)‖

/-- The translation length |E - G|.
    This is the length of translation by word w2 in the IET. -/
noncomputable def translation_length_2 : ℝ := ‖E - G‖

/-- The total segment length |E - E'| = 2|E|. -/
noncomputable def segment_length : ℝ := ‖E - E'‖

end TDCSG.Definitions
