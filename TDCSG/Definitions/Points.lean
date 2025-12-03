/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Geometry
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Special Points for the Critical Segment

This file defines the special points in the two-disk compound symmetry group `GG₅`
that are critical for establishing the interval exchange transformation (IET).

At the critical radius `r_crit = √(3 + φ)`, the segment from `E'` to `E` lies along
the boundary of the disk intersection and serves as the domain of the IET. The paper
(main.tex, Section "Geometric Constructions") proves that `GG₅` is infinite at this
radius by showing that three generator sequences permute subsegments of `E'E` in a
non-periodic pattern governed by the golden ratio.

## Main definitions

- `E`: The point `ζ₅⁴ - ζ₅³` on the boundary of the left disk
- `E'`: The point `-E`, on the boundary of the right disk
- `segmentPoint`: Linear parameterization of the segment from `E'` to `E`

## Mathematical context

The proof that `GG₅(r_crit)` is infinite relies on three key observations:
1. The segment `E'E` is partitioned into three parts by points `F` and `G`
2. Specific generator sequences translate these parts onto each other
3. The ratio `|E - E'| / |F - F'| = φ` (golden ratio) ensures non-periodicity

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
* main.tex, Section "Geometric Constructions" and Theorem "GG₅ is infinite at r = √(3 + φ)"
-/

namespace TDCSG.Definitions

open Complex Real

/-- The point `E = ζ₅⁴ - ζ₅³` on the boundary of the left disk at critical radius.

This point lies on the circle of radius `r_crit = √(3 + φ)` centered at `-1`.
In the paper's notation (main.tex Section "Geometric Constructions"), this corresponds
to the point `E` satisfying `|E + 1| = r`, where the segment `E'E` defines the domain
of the interval exchange transformation.

Together with its reflection `E' = -E`, this point defines the critical segment
on which the three piecewise translations act, generating infinite orbits at the
critical radius. -/
noncomputable def E : ℂ := ζ₅^4 - ζ₅^3

/-- The point `E' = -E`, the opposite endpoint of the critical segment.

By symmetry of the two-disk configuration about the origin, `E'` lies on the
boundary of the right disk at critical radius. The segment from `E'` to `E`
passes through the origin and is invariant under the piecewise translations
induced by `GG₅`.

The three subsegments `E'F'`, `F'G'`, and `G'E` (where `F` and `G` are defined
via the parameter `t_G`) are permuted by specific generator sequences, establishing
the interval exchange transformation structure. -/
noncomputable def E' : ℂ := -E

/-- Parameterization of the segment from `E'` to `E` by parameter `t ∈ [0,1]`.

The linear parameterization is defined as `segmentPoint t = E' + t * (E - E')`, giving:
- `segmentPoint 0 = E'` (start of segment)
- `segmentPoint 1 = E` (end of segment)
- `segmentPoint 0.5 = 0` (origin, midpoint by symmetry)

This parameterization is used to define the interval exchange transformation (IET).
The critical points `F` and `G` on this segment correspond to specific parameter
values that divide the segment into three parts exchanged by the generator
sequences from the proof in main.tex. -/
noncomputable def segmentPoint (t : ℝ) : ℂ := E' + t • (E - E')

end TDCSG.Definitions
