/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.GG10.Core

/-!
# Special Points for the GG(10,10) Critical Segment

This file defines the special points in the two-disk compound symmetry group GG(10,10)
that are critical for establishing the interval exchange transformation (IET).

At the critical radius `r_crit_10 = √(4 - φ) ≈ 1.543`, the segment from `E'₁₀` to `E₁₀`
serves as the domain of the IET. Unlike GG5's 3-interval IET, GG10 induces a simpler
2-interval IET with rotation number 1/φ.

## Main definitions

- `E₁₀`: The point `ζ₁₀ - ζ₁₀²` on the boundary of the disk intersection
- `E'₁₀`: The point `-E₁₀`, the conjugate endpoint
- `segmentPoint₁₀`: Linear parameterization of the segment from `E'₁₀` to `E₁₀`

## Mathematical context

The segment E'₁₀E₁₀ has length √(6 - 2√5) = √5 - 1 = 2/φ ≈ 1.236.

The 2-interval IET partitions [0,1] at 1/φ ≈ 0.618:
- J₁ = [0, 1/φ): translates by +0.382 = 2-φ via word w₁
- J₂ = [1/φ, 1): translates by -0.618 = -1/φ via word w₂

Since the rotation number 1/φ is irrational, almost all orbits are infinite.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.GG10

open Complex Real
open TDCSG.Definitions (φ)

/-- The point `E₁₀ = ζ₁₀ - ζ₁₀²` defining one endpoint of the critical segment.

This point lies on the boundary of the disk intersection at critical radius.
In Cartesian coordinates: E₁₀ = (0.5, sin(π/5) - sin(2π/5)) ≈ (0.5, -0.363271).

Together with its negation `E'₁₀ = -E₁₀`, this point defines the critical segment
on which the 2-interval IET acts. -/
noncomputable def E₁₀ : ℂ := ζ₁₀ - ζ₁₀^2

/-- The point `E'₁₀ = -E₁₀`, the opposite endpoint of the critical segment.

By symmetry of the two-disk configuration about the origin, `E'₁₀` lies
opposite to `E₁₀`. The segment from `E'₁₀` to `E₁₀` passes through the origin. -/
noncomputable def E'₁₀ : ℂ := -E₁₀

/-- Parameterization of the segment from `E'₁₀` to `E₁₀` by parameter `t ∈ [0,1]`.

The linear parameterization is defined as `segmentPoint₁₀ t = E'₁₀ + t * (E₁₀ - E'₁₀)`, giving:
- `segmentPoint₁₀ 0 = E'₁₀` (start of segment)
- `segmentPoint₁₀ 1 = E₁₀` (end of segment)
- `segmentPoint₁₀ 0.5 = 0` (origin, midpoint by symmetry)

This parameterization is used to define the 2-interval IET. The boundary at t = 1/φ
divides the segment into two parts exchanged by the generator sequences w₁ and w₂. -/
noncomputable def segmentPoint₁₀ (t : ℝ) : ℂ := E'₁₀ + t • (E₁₀ - E'₁₀)

/-! ### Basic Properties -/

/-- E'₁₀ is the negation of E₁₀. -/
@[simp] lemma E'₁₀_eq_neg : E'₁₀ = -E₁₀ := rfl

/-- The segment from E'₁₀ to E₁₀ has span 2*E₁₀. -/
lemma segment_span : E₁₀ - E'₁₀ = 2 * E₁₀ := by
  unfold E'₁₀
  ring

/-- segmentPoint₁₀ 0 = E'₁₀ -/
@[simp] lemma segmentPoint₁₀_zero : segmentPoint₁₀ 0 = E'₁₀ := by
  unfold segmentPoint₁₀
  simp

/-- segmentPoint₁₀ 1 = E₁₀ -/
@[simp] lemma segmentPoint₁₀_one : segmentPoint₁₀ 1 = E₁₀ := by
  unfold segmentPoint₁₀
  simp [E'₁₀_eq_neg]

/-- segmentPoint₁₀ 0.5 = 0 (the origin is the midpoint). -/
@[simp] lemma segmentPoint₁₀_half : segmentPoint₁₀ (1/2) = 0 := by
  unfold segmentPoint₁₀
  simp [E'₁₀_eq_neg]
  ring

/-- Alternative form: segmentPoint₁₀ in terms of E₁₀. -/
lemma segmentPoint₁₀_eq : segmentPoint₁₀ t = -E₁₀ + t • (2 * E₁₀) := by
  unfold segmentPoint₁₀ E'₁₀
  congr 1
  ring

/-- Linear relationship between segmentPoint₁₀ values. -/
lemma segmentPoint₁₀_linear (s t : ℝ) :
    segmentPoint₁₀ s - segmentPoint₁₀ t = (s - t) • (E₁₀ - E'₁₀) := by
  unfold segmentPoint₁₀
  simp only [sub_smul]
  ring

end TDCSG.GG10
