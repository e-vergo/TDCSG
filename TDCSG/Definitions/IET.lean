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

/- Why displacement0 = displacement1:

The IET describes a cyclic permutation (0 → 1 → 2 → 0). Under this permutation:
- Interval 0 (at domain position 0) maps to range position 1
- Interval 1 (at domain position 1) maps to range position 2
- Interval 2 (at domain position 2) maps to range position 0

Both intervals 0 and 1 move "forward" by one position in the range ordering,
which geometrically means they both jump over interval 2 (of length ψ).
Hence both receive displacement +ψ = length3.

Interval 2 moves "backward" to position 0, jumping over both intervals 0 and 1
(combined length ψ²). Hence it receives displacement -(length1 + length2) = -ψ².

Note: displacement0 + displacement1 + displacement2 * (length3 / length1) = 0
captures the measure-preserving property of the IET. -/

/-- Displacement for interval 0: d_0 = length3 = ψ ≈ 0.618.
    Points in [E', F') are translated by ψ to [G, F). -/
noncomputable def displacement0 : ℝ := length3

/-- Displacement for interval 1: d_1 = length3 = ψ ≈ 0.618.
    Points in [F', G') are translated by ψ to [F, E). -/
noncomputable def displacement1 : ℝ := length3

/-- Displacement for interval 2: d_2 = -(length1 + length2) = -ψ² ≈ -0.382.
    Points in [G', E) are translated by -ψ² to [E', G). -/
noncomputable def displacement2 : ℝ := -(length1 + length2)

/-! ### Supporting lemmas for IET construction -/

/-- 1 + φ is positive. -/
private lemma one_plus_phi_pos : 0 < 1 + Real.goldenRatio := by
  have h1 : 0 < Real.goldenRatio := Real.goldenRatio_pos
  linarith

/-- The first interval length is positive. -/
lemma length1_pos : 0 < length1 := by
  unfold length1
  exact div_pos one_pos (by linarith [one_plus_phi_pos])

/-- The second interval length is positive. -/
lemma length2_pos : 0 < length2 := by
  unfold length2
  exact div_pos one_pos (by linarith [one_plus_phi_pos])

/-- The third interval length is positive. -/
lemma length3_pos : 0 < length3 := by
  unfold length3
  exact div_pos one_pos Real.goldenRatio_pos

/-- The three interval lengths sum to one. -/
lemma lengths_sum_to_one : length1 + length2 + length3 = 1 := by
  unfold length1 length2 length3
  have h_phi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have h_one_plus_phi_pos : 0 < 1 + Real.goldenRatio := one_plus_phi_pos
  have h_phi_ne : Real.goldenRatio ≠ 0 := ne_of_gt h_phi_pos
  have h_one_plus_phi_ne : 1 + Real.goldenRatio ≠ 0 := ne_of_gt h_one_plus_phi_pos
  have h_two_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_sq := Real.goldenRatio_sq
  have h_key : Real.goldenRatio * (1 + Real.goldenRatio) = 1 + 2 * Real.goldenRatio := by
    calc Real.goldenRatio * (1 + Real.goldenRatio)
        = Real.goldenRatio + Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio + (Real.goldenRatio + 1) := by rw [h_sq]
      _ = 1 + 2 * Real.goldenRatio := by ring
  have h_sum : Real.goldenRatio + (1 + Real.goldenRatio) = 1 + 2 * Real.goldenRatio := by ring
  have h_prod_pos : 0 < Real.goldenRatio * (1 + Real.goldenRatio) := by positivity
  have h_prod_ne : Real.goldenRatio * (1 + Real.goldenRatio) ≠ 0 := ne_of_gt h_prod_pos
  calc 1 / (2 * (1 + Real.goldenRatio)) + 1 / (2 * (1 + Real.goldenRatio)) + 1 / Real.goldenRatio
      = 2 / (2 * (1 + Real.goldenRatio)) + 1 / Real.goldenRatio := by ring
    _ = 1 / (1 + Real.goldenRatio) + 1 / Real.goldenRatio := by
        congr 1; field_simp
    _ = (Real.goldenRatio + (1 + Real.goldenRatio)) / (Real.goldenRatio * (1 + Real.goldenRatio)) := by
        field_simp
    _ = (1 + 2 * Real.goldenRatio) / (Real.goldenRatio * (1 + Real.goldenRatio)) := by rw [h_sum]
    _ = (1 + 2 * Real.goldenRatio) / (1 + 2 * Real.goldenRatio) := by rw [h_key]
    _ = 1 := by field_simp

/-! ### IET Definitions -/

/-- The critical radius for GG(5,5). -/
noncomputable def criticalRadius : ℝ :=
  Real.sqrt (3 + Real.goldenRatio)

/-- Predicate: an IET emerges from the system dynamics at radius r. -/
def HasEmergentIET (r : ℝ) : Prop :=
  r = Real.sqrt (3 + Real.goldenRatio)

/-- The cyclic permutation (0 → 1 → 2 → 0) on Fin 3.
    This permutation maps:
    - Interval 0 [E', F') to range position 1 [G, F)
    - Interval 1 [F', G') to range position 2 [F, E)
    - Interval 2 [G', E) to range position 0 [E', G) -/
def cyclicPerm3 : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2

/-- The 3-interval exchange transformation induced by GG(5,5)
dynamics at criticality.

The permutation is cyclic (0 → 1 → 2 → 0), matching the paper geometry:
- Word1 maps E'F' → GF (domain 0 → range 1)
- Word2 maps F'G' → FE (domain 1 → range 2)
- Word3 maps G'E → E'G (domain 2 → range 0) -/
noncomputable def GG5_induced_IET : IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i =>
    if i = 0 then length1
    else if i = 1 then length2
    else length3
  lengths_pos := by
    intro i
    fin_cases i
    all_goals simp only [ite_true, ite_false]
    · exact length1_pos
    · exact length2_pos
    · exact length3_pos
  lengths_sum := by
    have h_univ : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [h_univ]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [show (1 : Fin 3) = 0 ↔ False by decide,
                 show (2 : Fin 3) = 0 ↔ False by decide,
                 show (2 : Fin 3) = 1 ↔ False by decide,
                 ite_true, ite_false]
      have h := lengths_sum_to_one
      ring_nf at h ⊢
      exact h
    · decide
    · decide
  permutation := cyclicPerm3

/-- The emergent IET at a given radius. -/
noncomputable def EmergentIET (r : ℝ) (_ : HasEmergentIET r) :
    IntervalExchangeTransformation 3 :=
  GG5_induced_IET

end TDCSG.Definitions
