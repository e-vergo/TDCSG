/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat, Eric Hearn
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Interval Exchange Transformation Definitions

This file contains core definitions for interval exchange transformations (IETs).

## Main definitions

### Core IET structure
- `IntervalExchangeTransformation n`: An IET with `n` intervals

### Interval endpoints
- `domainLeft`, `domainRight`: Left and right endpoints of domain intervals
- `rangeLeft`, `rangeRight`: Left and right endpoints of range intervals

### Interval sets
- `interval`: The ith subinterval in the domain

### Standard examples
- `IET_two_intervals`: 2-interval IET from a single parameter
- `IET_identity`: Identity IET (1 interval)
- `IET_three_example`: 3-interval IET example
- `IET_inverse`: Inverse of an IET

### Golden ratio IET lengths
- `length1`, `length2`, `length3`: Lengths for GG5-induced IET
- `displacement0`, `displacement1`, `displacement2`: Displacements for GG5-induced IET
-/

universe u

open Set

/-- An interval exchange transformation on `n` intervals.

Given `n` intervals with specified lengths and a permutation, an IET rearranges these intervals
according to the permutation while preserving orientation within each interval. -/
structure IntervalExchangeTransformation (n : ℕ) where
  /-- We require at least one interval -/
  n_pos : 0 < n
  /-- The lengths of the intervals -/
  lengths : Fin n → ℝ
  /-- All lengths are positive -/
  lengths_pos : ∀ i, 0 < lengths i
  /-- The lengths sum to 1 (normalized) -/
  lengths_sum : ∑ i, lengths i = 1
  /-- The permutation describing how intervals are rearranged -/
  permutation : Equiv.Perm (Fin n)

namespace IntervalExchangeTransformation

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/-- The left endpoint of the ith interval in the domain (before permutation). -/
noncomputable def domainLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths ⟨j, Nat.lt_trans j.isLt i.isLt⟩

/-- The right endpoint of the ith interval in the domain. -/
noncomputable def domainRight (i : Fin n) : ℝ :=
  iet.domainLeft i + iet.lengths i

/-- The left endpoint of the ith interval in the range (after permutation).
    The range ordering places interval π⁻¹(j) at position j, so rangeLeft(i)
    sums the lengths of intervals π⁻¹(0), π⁻¹(1), ..., π⁻¹(i-1). -/
noncomputable def rangeLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths (iet.permutation.symm ⟨j, Nat.lt_trans j.isLt i.isLt⟩)

/-- The right endpoint of the ith interval in the range. -/
noncomputable def rangeRight (i : Fin n) : ℝ :=
  iet.rangeLeft i + iet.lengths (iet.permutation i)

/-- The ith subinterval in the domain. -/
noncomputable def interval (i : Fin n) : Set ℝ :=
  Ico (iet.domainLeft i) (iet.domainRight i)

/-- The transformation function for the IET.

For a point x in [0,1), determine which interval i contains x, then
map it to the corresponding position in the permuted interval permutation(i).
Specifically: x in [domainLeft i, domainRight i) maps to
rangeLeft (permutation i) + (x - domainLeft i).

Outside [0,1), the function returns x unchanged. -/
noncomputable def toFun : ℝ → ℝ := fun x =>
  Classical.epsilon fun y => ∃ i, x ∈ iet.interval i ∧
    y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)

end IntervalExchangeTransformation

section TwoIntervals

/-- A 2-interval exchange is determined by a single parameter alpha in (0,1). -/
def IET_two_intervals (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    IntervalExchangeTransformation 2 where
  n_pos := by norm_num
  lengths := fun i => if i = 0 then α else 1 - α
  lengths_pos := by
    intro i
    simp only [mem_Ioo] at hα
    by_cases h : i = 0
    · simp [h]; exact hα.1
    · simp [h]; linarith
  lengths_sum := by
    have : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [this, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
    norm_num [if_pos, if_neg]
  permutation := Equiv.swap 0 1

end TwoIntervals

section GeneralProperties

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/-- An IET is invertible. -/
noncomputable def IET_inverse : IntervalExchangeTransformation n where
  n_pos := iet.n_pos
  lengths := fun i => iet.lengths (iet.permutation.symm i)
  lengths_pos := by intro i; exact iet.lengths_pos (iet.permutation.symm i)
  lengths_sum := by
    have : ∑ i, iet.lengths (iet.permutation.symm i) = ∑ i, iet.lengths i := by
      exact iet.permutation.symm.sum_comp iet.lengths
    rw [this]; exact iet.lengths_sum
  permutation := iet.permutation.symm

end GeneralProperties

section Examples

/-- The identity IET: trivial permutation, single interval. -/
def IET_identity : IntervalExchangeTransformation 1 where
  n_pos := by norm_num
  lengths := fun _ => 1
  lengths_pos := by intro; norm_num
  lengths_sum := by simp
  permutation := Equiv.refl _

/-- A 3-interval exchange example. -/
def IET_three_example (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hsum : α + β < 1) :
    IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i => if i = 0 then α else if i = 1 then β else 1 - α - β
  lengths_pos := by
    intro i; fin_cases i
    · simp; exact hα
    · simp; exact hβ
    · simp; linarith
  lengths_sum := by
    have : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [this, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [show (2 : Fin 3) = 0 ↔ False by decide, show (2 : Fin 3) = 1 ↔ False by decide,
                 show (1 : Fin 3) = 0 ↔ False by decide]
      simp only [ite_true, ite_false]; ring
    · decide
    · decide
  permutation := Equiv.swap 0 2

end Examples

/-! ## Golden ratio IET definitions

Based on the paper geometry, the segment E'E is divided into three sub-segments:
- [E', F') of length ψ²/2 ≈ 0.191
- [F', G') of length ψ²/2 ≈ 0.191
- [G', E) of length ψ ≈ 0.618

where ψ = (√5-1)/2 = 1/φ is the golden conjugate (positive version).

The IET permutation is cyclic: (0 → 1 → 2 → 0), mapping:
- E'F' → GF (interval 0 → range position 1)
- F'G' → FE (interval 1 → range position 2)
- G'E → E'G (interval 2 → range position 0)
-/

namespace TDCSG.Definitions

open Real

/-- First interval length: |E'F'| = ψ²/2 = 1/(2(1+φ)) ≈ 0.191.
    This is the length of segment from E' to F'. -/
noncomputable def length1 : ℝ :=
  1 / (2 * (1 + goldenRatio))

/-- Second interval length: |F'G'| = ψ²/2 = 1/(2(1+φ)) ≈ 0.191.
    This is the length of segment from F' to G'. -/
noncomputable def length2 : ℝ :=
  1 / (2 * (1 + goldenRatio))

/-- Third interval length: |G'E| = ψ = 1/φ ≈ 0.618.
    This is the length of segment from G' to E. -/
noncomputable def length3 : ℝ :=
  1 / goldenRatio

/-- Displacement for interval 0: d_0 = length3 = ψ ≈ 0.618.
    Points in [E', F') are translated by ψ to [G, F). -/
noncomputable def displacement0 : ℝ := length3

/-- Displacement for interval 1: d_1 = length3 = ψ ≈ 0.618.
    Points in [F', G') are translated by ψ to [F, E). -/
noncomputable def displacement1 : ℝ := length3

/-- Displacement for interval 2: d_2 = -(length1 + length2) = -ψ² ≈ -0.382.
    Points in [G', E) are translated by -ψ² to [E', G). -/
noncomputable def displacement2 : ℝ := -(length1 + length2)

end TDCSG.Definitions
