/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.MainTheorem
import TDCSG.Geometry

/-!
# Proof of Main Theorem

This file provides the proof that GG5 is infinite at the critical radius.

## Main results

* `mainTheorem` : GG5 is infinite at r_crit = sqrt(3 + phi).

## Proof structure

The proof proceeds through several layers:

1. **Geometric setup** (Geometry.lean): Define the critical radius r_crit = sqrt(3 + phi)
   and verify key geometric properties of the disk configuration.

2. **IET construction** (IET.lean): Show that the group action on segment E'E induces
   an interval exchange transformation with three intervals.

3. **Golden ratio irrationality** (OrbitInfinite.lean): Prove that the interval lengths
   are in golden ratio proportions, making the rotation irrational.

4. **Linear independence** (OrbitInfinite.lean): Prove that {1, phi} is linearly
   independent over Z, which prevents periodic orbits.

5. **Infinite orbit** (OrbitInfinite.lean): Use the algebraic constraints to show
   that no finite orbit can exist, hence orbits are infinite.

## References

* Two-Disk Compound Symmetry Groups, Hearn et al., arXiv:2302.12950v1
-/

/-- **Main Theorem**: GG5 is infinite at the critical radius.

This theorem establishes that the two-disk compound symmetry group GG5 = GG(5,5)
is infinite when the disks are positioned at the critical radius r_crit = sqrt(3 + phi),
where phi = (1 + sqrt5)/2 is the golden ratio.

The proof shows that there exists a point whose orbit under the group action is unbounded.
Specifically, we find a point on segment E'E whose iterates under the induced interval
exchange transformation are all distinct, using the irrationality of the golden ratio
and the linear independence of {1, phi} over Z. -/
theorem mainTheorem : StatementOfTheorem := by
  -- Get x₀ ∈ [0,1) with infinite IET orbit
  obtain ⟨x₀, hx₀_mem, hx₀_inf⟩ := CompoundSymmetry.GG5.GG5_IET_has_infinite_orbit
  -- The point on segment E'E corresponding to x₀
  let p := TDCSG.CompoundSymmetry.GG5.segmentPointPlane x₀
  use p
  -- The IET orbit being infinite implies the group orbit is infinite
  exact TDCSG.CompoundSymmetry.GG5.IET_orbit_infinite_implies_group_orbit_infinite x₀ hx₀_mem hx₀_inf
