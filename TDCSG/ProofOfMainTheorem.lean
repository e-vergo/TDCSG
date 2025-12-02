/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.MainTheorem
import TDCSG.Proofs.GroupTheory

/-!
# Proof of Theorem 2: The Compound Symmetry Group GG₅ is Infinite

This file contains the proof that the compound symmetry group GG(5,5) at the
critical radius r_crit = √(3 + φ) is infinite.

## Proof Strategy

The proof proceeds in four stages:

### Stage 1: Interval Exchange Transformation (IET) Construction

We identify a segment E'E in the intersection of the two disks where the group
action reduces to an interval exchange transformation. The segment is partitioned
into three intervals I₁, I₂, I₃ with lengths in golden ratio proportions:

    |I₁| : |I₂| : |I₃| = 1 : φ : φ²

where φ = (1 + √5)/2 is the golden ratio.

The IET permutes these intervals via translations that correspond to specific
words in generators A and B.

### Stage 2: Infinite IET Orbit

The key arithmetic fact: {1, φ} are linearly independent over ℤ.

This means no non-trivial integer linear combination of the translation amounts
equals zero, which implies the IET has no periodic orbits for generic starting
points. In particular, there exists a point x₀ ∈ [0,1) whose IET orbit is infinite.

This is proven via:
- `phi_irrational` : φ is irrational
- `GG5_IET_has_infinite_orbit` : ∃ x₀, (IET orbit of x₀).Infinite

### Stage 3: Orbit Correspondence

The word-based orbit of points in ℂ under generators A, B corresponds exactly
to the MulAction orbit under the subgroup `GG5_At_Critical_radius`:

    orbit r z = groupOrbit r z = MulAction.orbit GG5_At_Critical_radius z

This equivalence is established via:
- `word_orbit_subset_group_orbit` : Every word gives a group element
- `group_orbit_subset_word_orbit` : Every group element corresponds to a word
- `orbit_eq_groupOrbit` : The orbits are equal

The IET infinite orbit lifts to an infinite word-based orbit, which equals
the MulAction orbit of the subgroup.

### Stage 4: Infinite Orbit Implies Infinite Group

The final logical step uses the contrapositive of a fundamental result:

    Finite G ⟹ (∀ z, MulAction.orbit G z is finite)

Equivalently:

    (∃ z, MulAction.orbit G z is infinite) ⟹ Infinite G

This is `infinite_orbit_implies_infinite_group` in Proofs/GroupTheory.lean.

## Conclusion

Combining all stages:
1. The IET has a point with infinite orbit (Stage 2)
2. This lifts to an infinite word-based orbit (Stage 3)
3. The word-based orbit equals the MulAction orbit (Stage 3)
4. An infinite MulAction orbit implies the group is infinite (Stage 4)

Therefore: `Infinite GG5_At_Critical_radius`

## References

* Two-Disk Compound Symmetry Groups, Hearn et al., arXiv:2302.12950v1
-/

open TDCSG.Definitions TDCSG.CompoundSymmetry.GG5

/-- **Theorem 2**: The compound symmetry group GG₅ is infinite at the critical radius.

The compound symmetry group GG(5,5) at r_crit = √(3 + φ) is an infinite group.

**Proof outline:**

1. **IET infinite orbit**: From `GG5_IET_has_infinite_orbit`, we obtain a point x₀
   in [0,1) whose IET orbit is infinite.

2. **Lift to group orbit**: `IET_orbit_infinite_implies_group_orbit_infinite`
   shows that the corresponding point `segmentPoint x₀` has infinite word-based orbit.

3. **Orbit equivalence**: `orbit_eq_groupOrbit` establishes that the word-based
   orbit equals the MulAction orbit of the subgroup.

4. **Infinite group**: `infinite_orbit_implies_infinite_group` concludes that
   having an infinite orbit implies the group itself is infinite. -/
theorem GG5_infinite_at_critical_radius : StatementOfTheorem := by
  -- Stage 1-2: Obtain a point with infinite IET orbit
  -- GG5_IET_has_infinite_orbit : ∃ x₀ ∈ [0,1), (IET orbit of x₀).Infinite
  obtain ⟨x₀, hx₀_mem, hx₀_inf⟩ := GG5_IET_has_infinite_orbit

  -- Stage 3a: Lift IET infinite orbit to word-based infinite orbit
  -- IET_orbit_infinite_implies_group_orbit_infinite shows segmentPoint x₀ has infinite orbit
  have h_word_inf : (orbit r_crit (segmentPoint x₀)).Infinite :=
    IET_orbit_infinite_implies_group_orbit_infinite x₀ hx₀_mem hx₀_inf

  -- Stage 3b: Word-based orbit equals MulAction orbit of the subgroup
  -- orbit_eq_groupOrbit : orbit r z = groupOrbit r z
  rw [orbit_eq_groupOrbit] at h_word_inf

  -- Stage 4: Infinite MulAction orbit implies infinite group
  -- infinite_orbit_implies_infinite_group : orbit infinite ⟹ group infinite
  exact infinite_orbit_implies_infinite_group (segmentPoint x₀) h_word_inf
