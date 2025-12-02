/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.MainTheorem
import TDCSG.Proofs.GroupTheory

/-!
# Proof of Main Theorem

This file provides the proof that the compound symmetry group GG5 is infinite
at the critical radius.

## Main results

* `GG5_infinite_at_critical_radius` : The compound symmetry group GG5 is infinite.

## Proof structure

The proof proceeds in layers:

1. **Geometric setup** (Points.lean):
   - Critical points E, E', F, G defined on segment in disk intersection

2. **IET structure** (IET.lean):
   - Three-interval exchange transformation on segment E'E
   - Interval lengths in golden ratio proportions: 1 : φ : φ²

3. **Word correspondence** (Word*Correspondence.lean):
   - Group words implement IET translations
   - IET orbit maps injectively to group orbit

4. **Infinite IET orbit** (OrbitInfinite.lean):
   - Linear independence of {1, φ} over ℤ prevents periodic orbits
   - `GG5_IET_has_infinite_orbit` provides a point with infinite orbit

5. **Group theory bridge** (GroupTheory.lean):
   - Word-based orbit equals MulAction orbit of the subgroup
   - Infinite orbit implies infinite group (contrapositive of finite group ⟹ finite orbits)

6. **Conclusion**:
   - ∃ point with infinite orbit ⟹ GG5 is infinite as a group

## References

* Two-Disk Compound Symmetry Groups, Hearn et al., arXiv:2302.12950v1
-/

open TDCSG.Definitions TDCSG.CompoundSymmetry.GG5

/-- **Theorem 2**: The compound symmetry group GG5 is infinite at the critical radius.

The compound symmetry group GG(5,5) at r_crit = √(3 + φ) is an infinite group.

The proof shows:
1. There exists a point z ∈ ℂ whose orbit under GG5 is infinite
2. An infinite orbit implies an infinite group

This is the complete, group-theoretically correct formalization of Theorem 2
from arXiv:2302.12950v1. -/
theorem GG5_infinite_at_critical_radius : StatementOfTheorem :=
  GG5_is_infinite
