/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.MainTheorem
import TDCSG.Proofs.Geometry

/-!
# Proof of Main Theorem

This file provides the proof that GG5 is infinite at the critical radius.

## Main results

* `GG5_infinite_at_critical_radius` : GG5 is infinite at r_crit = sqrt(3 + phi).

## Proof structure

The proof uses the chain:

1. **Geometric setup** (Points.lean, PlaneConversion.lean):
   - Critical points E, E', F, G defined
   - Segment E'E lies in disk intersection

2. **Translation irrationality** (SegmentGeometry.lean):
   - Interval lengths are in golden ratio proportions

3. **IET structure** (IET.lean):
   - Three-interval exchange transformation on segment E'E

4. **Word correspondence** (WordCorrespondence.lean):
   - Group words implement IET translations
   - IET orbit maps to group orbit

5. **Infinite orbit** (OrbitInfinite.lean):
   - Linear independence of {1, φ} over ℤ prevents periodic orbits
   - `GG5_IET_has_infinite_orbit` provides the witness

## References

* Two-Disk Compound Symmetry Groups, Hearn et al., arXiv:2302.12950v1
-/

open TDCSG.Definitions TDCSG.CompoundSymmetry.GG5

/-- **Theorem 2**: GG5 is infinite at the critical radius r_crit = sqrt(3 + φ).

The compound symmetry group GG(5,5) is infinite when the disks are positioned at
the critical radius. The proof finds a point on segment E'E whose orbit under the
induced interval exchange transformation is infinite, then lifts this to an infinite
group orbit using word correspondence. -/
theorem GG5_infinite_at_critical_radius : StatementOfTheorem := by
  -- Get x₀ ∈ [0,1) with infinite IET orbit
  obtain ⟨x₀, hx₀_mem, hx₀_inf⟩ := GG5_IET_has_infinite_orbit
  -- The point on segment E'E corresponding to x₀
  use segmentPointPlane x₀
  -- The IET orbit being infinite implies the group orbit is infinite
  exact IET_orbit_infinite_implies_group_orbit_infinite x₀ hx₀_mem hx₀_inf
