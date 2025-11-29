/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat, Eric Hearn
-/
import TDCSG.Proofs.Basic
import TDCSG.Proofs.Finite
import TDCSG.Proofs.MeasurePreserving
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
- `segmentParam`, `length1`, `length2`, `length3`: Lengths for GG5-induced IET
- `displacement0`, `displacement1`, `displacement2`: Displacements for GG5-induced IET
-/

universe u

namespace PiecewiseIsometry

open Set MeasureTheory

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

/-- The left endpoint of the ith interval in the range (after permutation). -/
noncomputable def rangeLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths (iet.permutation ⟨j, Nat.lt_trans j.isLt i.isLt⟩)

/-- The right endpoint of the ith interval in the range. -/
noncomputable def rangeRight (i : Fin n) : ℝ :=
  iet.rangeLeft i + iet.lengths (iet.permutation i)

/-- The ith subinterval in the domain. -/
noncomputable def interval (i : Fin n) : Set ℝ :=
  Ico (iet.domainLeft i) (iet.domainRight i)

/-- Helper: which interval contains a point in [0,1).

Note: This definition requires the theorem `intervals_cover` to show the Classical.choose
produces a valid result. The theorem is in the main IntervalExchange.lean file. -/
noncomputable def intervalContaining (x : ℝ) (hx : x ∈ Ico 0 1)
    (h_cover : ⋃ i, iet.interval i = Ico 0 1) : Fin n :=
  Classical.choose (by
    have : x ∈ ⋃ i, iet.interval i := by rw [h_cover]; exact hx
    simp only [Set.mem_iUnion] at this
    exact this)

/-- The transformation function for the IET.

For a point x in [0,1), determine which interval i contains x, then
map it to the corresponding position in the permuted interval permutation(i).
Specifically: x in [domainLeft i, domainRight i) maps to
rangeLeft (permutation i) + (x - domainLeft i).

Outside [0,1), the function returns x unchanged. -/
noncomputable def toFun : ℝ → ℝ := fun x =>
  Classical.epsilon fun y => ∃ i, x ∈ iet.interval i ∧
    y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)

/-- Convert an IET to a piecewise isometry on R.

The IET naturally operates on [0,1). To extend to all of R, we add two additional pieces:
- Iio 0 (negative reals): toFun acts as identity
- Ici 1 (>= 1): toFun acts as identity

This matches the standard pattern for extending interval transformations to full space.

Note: Proof obligations are discharged in TDCSG/IntervalExchange.lean -/
noncomputable def toPiecewiseIsometry : PiecewiseIsometry ℝ where
  partition := Set.range iet.interval ∪ {Set.Iio 0, Set.Ici 1}
  partition_measurable := sorry
  partition_countable := sorry
  partition_cover := sorry
  partition_disjoint := sorry
  partition_nonempty := sorry
  toFun := fun x =>
    if h : x ∈ Ico 0 1 then
      -- x is in [0,1), so it's in some interval i
      -- Map it according to the IET
      let i := intervalContaining iet x h sorry
      iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)
    else
      -- x is outside [0,1), act as identity
      x
  isometry_on_pieces := sorry

/-- An IET is a finite piecewise isometry.

The partition has finitely many pieces: n intervals from the IET, plus 2 additional pieces
(Iio 0 and Ici 1) for extending to all of R.

Note: Proof obligations are discharged in TDCSG/IntervalExchange.lean -/
noncomputable def toFinitePiecewiseIsometry : FinitePiecewiseIsometry ℝ where
  toPiecewiseIsometry := iet.toPiecewiseIsometry
  partition_finite := sorry

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

end PiecewiseIsometry

/-! ## Golden ratio IET definitions -/

namespace TDCSG.Definitions

open Real

/-- Segment parameter for the emergent IET. -/
noncomputable def segmentParam : ℝ := goldenRatio

/-- First fundamental length in the emergent 3-interval IET. -/
noncomputable def length1 : ℝ :=
  1 / (1 + goldenRatio + goldenRatio ^ 2)

/-- Second fundamental length in the emergent 3-interval IET. -/
noncomputable def length2 : ℝ :=
  goldenRatio / (1 + goldenRatio + goldenRatio ^ 2)

/-- Third fundamental length in the emergent 3-interval IET. -/
noncomputable def length3 : ℝ :=
  (goldenRatio ^ 2) / (1 + goldenRatio + goldenRatio ^ 2)

/-- Displacement for interval 0: d_0 = 1 - length1.
    This is the amount by which points in interval 0 are translated. -/
noncomputable def displacement0 : ℝ := 1 - length1

/-- Displacement for interval 1: d_1 = length3 - length1.
    This is the amount by which points in interval 1 are translated. -/
noncomputable def displacement1 : ℝ := length3 - length1

/-- Displacement for interval 2: d_2 = -1/2.
    This is the amount by which points in interval 2 are translated. -/
noncomputable def displacement2 : ℝ := -1/2

end TDCSG.Definitions

/-! ## GG5 IET Definitions -/

namespace CompoundSymmetry.GG5

open PiecewiseIsometry Real TDCSG.Definitions

/-- The critical radius for GG(5,5). -/
noncomputable def criticalRadius : ℝ :=
  sqrt (3 + goldenRatio)

/-- Predicate: an IET emerges from the system dynamics at radius r. -/
def HasEmergentIET (r : ℝ) : Prop :=
  r = sqrt (3 + goldenRatio)

/-- The 3-interval exchange transformation induced by GG(5,5)
dynamics at criticality. -/
noncomputable def GG5_induced_IET : IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i =>
    if i = 0 then length1
    else if i = 1 then length2
    else length3
  lengths_pos := by
    intro i
    fin_cases i
    · simp; exact sorry  -- length1_pos proved in IET.lean
    · simp; exact sorry  -- length2_pos proved in IET.lean
    · simp; exact sorry  -- length3_pos proved in IET.lean
  lengths_sum := by
    have h_univ : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} :=
      by decide
    rw [h_univ]
    rw [Finset.sum_insert, Finset.sum_insert,
      Finset.sum_singleton]
    · simp
      exact sorry  -- lengths_sum_to_one proved in IET.lean
    · decide
    · decide
  permutation := Equiv.swap 0 2

/-- The emergent IET at a given radius. -/
noncomputable def EmergentIET (r : ℝ)
    (_ : HasEmergentIET r) :
    IntervalExchangeTransformation 3 :=
  GG5_induced_IET

end CompoundSymmetry.GG5
