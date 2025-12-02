/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.MainTheorem
import TDCSG.Proofs.GroupTheory

/-!
# Proof of Main Theorem

This file contains the complete proof that GG(5,5) at the critical radius is infinite.

## Proof strategy

The proof proceeds by analyzing the induced interval exchange transformation (IET):

1. The group action on ℂ induces an IET on the segment E'E
2. The IET has three intervals with lengths in ratio 1 : φ : φ² (golden ratio structure)
3. Linear independence of {1, φ} over ℤ implies the IET has no periodic orbits
4. We construct a point x₀ with infinite IET orbit
5. The infinite IET orbit lifts to an infinite group orbit on ℂ
6. An infinite orbit implies the group is infinite

## Main statements

- `GG5_infinite_at_critical_radius`: Proof of `StatementOfTheorem`

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

open TDCSG.Definitions TDCSG.CompoundSymmetry.GG5

/-- **Main Theorem**: The compound symmetry group GG₅ at the critical radius is infinite. -/
theorem GG5_infinite_at_critical_radius : StatementOfTheorem := by
  obtain ⟨x₀, hx₀_mem, hx₀_inf⟩ := GG5_IET_has_infinite_orbit
  have h_word_inf : (orbit r_crit (segmentPoint x₀)).Infinite :=
    IET_orbit_infinite_implies_group_orbit_infinite x₀ hx₀_mem hx₀_inf
  rw [orbit_eq_groupOrbit] at h_word_inf
  exact infinite_orbit_implies_infinite_group (segmentPoint x₀) h_word_inf
