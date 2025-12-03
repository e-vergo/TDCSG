/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Real.GoldenRatio
import TDCSG.Definitions.WordCorrespondence

/-!
# Interval Exchange Transformation

This file defines interval exchange transformations (IETs) and specializes to the
3-interval IET induced by the GG5 group action at the critical radius.

## Main definitions

- `IntervalExchangeTransformation n`: A transformation partitioning [0,1] into n intervals
  and permuting them via translation
- `GG5_induced_IET`: The 3-interval IET induced by GG5 at r_crit
- `length1`, `length2`, `length3`: The three interval lengths (in ratio 1 : φ : φ²)
- `displacement0`, `displacement1`, `displacement2`: Translation displacements
- `IET_word x`: The word corresponding to applying the IET to point x
- `wordForIterate x k`: The word for the k-th iterate of the IET at x

## Implementation notes

The IET structure encodes:
- `n` intervals with positive lengths summing to 1
- A permutation determining how intervals are rearranged
- The transformation function `toFun` that applies the rearrangement

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

universe u

open Set

/--
An interval exchange transformation (IET) on `n` intervals of `[0,1]`.

An IET partitions the unit interval into `n` subintervals and rearranges them
according to a permutation, preserving Lebesgue measure. Each interval is
translated (without rotation or reflection) to its new position.

This structure encodes an IET by specifying:
- The number of intervals `n` (which must be positive)
- The lengths of each interval (positive reals summing to 1)
- A permutation describing how intervals are reordered

The transformation arises naturally in the study of two-disk compound symmetry
groups. At the critical radius for GG_5, the dynamics on the invariant line
segment E'E can be described by a 3-interval IET (see `GG5_induced_IET`).

## References
* Paper Section "Geometric Constructions": The proof that GG_5 is infinite at
  the critical radius proceeds by showing that three transformations act as
  translations on subsegments of E'E, forming an interval exchange.
-/
structure IntervalExchangeTransformation (n : ℕ) where
  /-- The number of intervals must be positive. -/
  n_pos : 0 < n
  /-- The lengths of the `n` intervals partitioning `[0,1]`. -/
  lengths : Fin n → ℝ
  /-- Each interval has strictly positive length. -/
  lengths_pos : ∀ i, 0 < lengths i
  /-- The interval lengths sum to 1, forming a partition of `[0,1]`. -/
  lengths_sum : ∑ i, lengths i = 1
  /-- The permutation describing how intervals are reordered. If `permutation i = j`,
      then the `i`-th interval in the domain maps to the `j`-th position in the range. -/
  permutation : Equiv.Perm (Fin n)

namespace IntervalExchangeTransformation

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/--
The left endpoint of the `i`-th domain interval.

Computed as the sum of lengths of all intervals with index less than `i`.
For `i = 0`, this equals `0`. The domain intervals partition `[0,1]` from
left to right in index order.
-/
noncomputable def domainLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths ⟨j, Nat.lt_trans j.isLt i.isLt⟩

/--
The right endpoint of the `i`-th domain interval.

Equals `domainLeft i + lengths i`. The `i`-th domain interval is
`[domainLeft i, domainRight i)`.
-/
noncomputable def domainRight (i : Fin n) : ℝ :=
  iet.domainLeft i + iet.lengths i

/--
The left endpoint of the `i`-th range interval (in permuted order).

After applying the IET, the intervals are reordered according to the
permutation. The `i`-th range interval receives the image of
`permutation.symm i`.
-/
noncomputable def rangeLeft (i : Fin n) : ℝ :=
  ∑ j : Fin i.val, iet.lengths (iet.permutation.symm ⟨j, Nat.lt_trans j.isLt i.isLt⟩)

/--
The right endpoint of the `i`-th range interval (in permuted order).

Equals `rangeLeft i + lengths (permutation i)`.
-/
noncomputable def rangeRight (i : Fin n) : ℝ :=
  iet.rangeLeft i + iet.lengths (iet.permutation i)

/--
The `i`-th domain interval as a set: `[domainLeft i, domainRight i)`.

This is a half-open interval, closed on the left and open on the right.
The domain intervals form a partition of `[0,1)`.
-/
noncomputable def interval (i : Fin n) : Set ℝ :=
  Ico (iet.domainLeft i) (iet.domainRight i)

/--
The interval exchange transformation as a function `ℝ → ℝ`.

For a point `x` in the `i`-th domain interval, the transformation translates
`x` to its corresponding position in the range interval determined by
`permutation i`. Points outside `[0,1)` have unspecified behavior.

The translation preserves the relative position within the interval:
`toFun x = rangeLeft (permutation i) + (x - domainLeft i)`
-/
noncomputable def toFun : ℝ → ℝ := fun x =>
  Classical.epsilon fun y => ∃ i, x ∈ iet.interval i ∧
    y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i)

end IntervalExchangeTransformation

section GeneralProperties

variable {n : ℕ} (iet : IntervalExchangeTransformation n)

/--
The inverse of an interval exchange transformation.

Constructed by applying the inverse permutation. Since IETs are bijections
that preserve measure, every IET has an inverse that is also an IET.
The inverse swaps domain and range roles:
- The lengths are reordered according to `permutation.symm`
- The new permutation is `permutation.symm`
-/
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

namespace TDCSG.Definitions

open Real

/--
Length of the first interval in the GG5-induced IET.

Equal to `1 / (2 * (1 + phi))` where `phi` is the golden ratio. In the
geometric interpretation from the paper, this corresponds to the segment
`E'F'` on the invariant line `E'E`, which is transformed by the move
sequence `a^(-2) b^(-1) a^(-1) b^(-1)`.

Note: `length1 = length2` due to symmetry. Together with `length3`, these
satisfy the ratio `1 : 1 : 2*phi`, normalized so their sum equals 1.
-/
noncomputable def length1 : ℝ :=
  1 / (2 * (1 + goldenRatio))

/--
Length of the second interval in the GG5-induced IET.

Equal to `1 / (2 * (1 + phi))`, the same as `length1`. Corresponds to
segment `F'G'` on the invariant line `E'E`, transformed by the move
sequence `a b a b^2`.
-/
noncomputable def length2 : ℝ :=
  1 / (2 * (1 + goldenRatio))

/--
Length of the third interval in the GG5-induced IET.

Equal to `1 / phi` where `phi` is the golden ratio. Corresponds to
segment `G'E` on the invariant line `E'E`, transformed by the move
sequence `a b a b^(-1) a^(-1) b^(-1)`.

The ratio `|E - E'| / |F - F'| = phi` is key to the proof that GG_5
is infinite at the critical radius, as this irrational ratio ensures
points can be mapped arbitrarily close to any position along `E'E`.
-/
noncomputable def length3 : ℝ :=
  1 / goldenRatio

/--
Translation displacement for the first interval.

Points in the first interval are translated forward by `length3`.
In the GG5 context, this corresponds to the translation component
of the piecewise isometry on segment `E'F'`.
-/
noncomputable def displacement0 : ℝ := length3

/--
Translation displacement for the second interval.

Points in the second interval are also translated forward by `length3`.
In the GG5 context, this corresponds to the translation component
of the piecewise isometry on segment `F'G'`.
-/
noncomputable def displacement1 : ℝ := length3

/--
Translation displacement for the third interval.

Points in the third interval are translated backward by `length1 + length2`.
This negative displacement moves points from the right portion of `[0,1]`
back toward the left, completing the cyclic exchange pattern.
-/
noncomputable def displacement2 : ℝ := -(length1 + length2)

/-- The first interval length is strictly positive. -/
lemma length1_pos : 0 < length1 := by
  unfold length1
  have := one_plus_phi_pos
  exact div_pos one_pos (by unfold φ at this; linarith)

/-- The second interval length is strictly positive. -/
lemma length2_pos : 0 < length2 := by
  unfold length2
  have := one_plus_phi_pos
  exact div_pos one_pos (by unfold φ at this; linarith)

/-- The third interval length is strictly positive. -/
lemma length3_pos : 0 < length3 := by
  unfold length3
  exact div_pos one_pos Real.goldenRatio_pos

/--
The three interval lengths sum to 1.

This is the key normalization ensuring `[0,1]` is partitioned exactly.
The proof uses the golden ratio identity `phi^2 = phi + 1` to simplify:
  `1/(2*(1+phi)) + 1/(2*(1+phi)) + 1/phi = 1`
-/
lemma lengths_sum_to_one : length1 + length2 + length3 = 1 := by
  unfold length1 length2 length3
  have h_phi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have h_one_plus_phi_pos : 0 < 1 + Real.goldenRatio := by
    show 0 < 1 + φ; exact one_plus_phi_pos
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

/--
The cyclic permutation `(0 1 2)` on `Fin 3`.

Sends `0 ↦ 1 ↦ 2 ↦ 0`. Constructed as the product of transpositions
`(0 1) * (1 2)`. This permutation describes how the three intervals
are cyclically exchanged in the GG5-induced IET.
-/
def cyclicPerm3 : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2

/--
The 3-interval IET induced by the GG_5 group action at critical radius.

At the critical radius `r = sqrt(3 + phi)`, the dynamics of GG_5 on the
invariant line segment `E'E` can be encoded as a 3-interval exchange
transformation. The three intervals have lengths in ratio `1 : 1 : 2*phi`
(normalized to sum to 1), and are cyclically permuted.

## Paper Reference
From the proof that GG_5 is infinite at critical radius:
- Segment `E'F'` maps to `GF` via `a^(-2) b^(-1) a^(-1) b^(-1)`
- Segment `F'G'` maps to `FE` via `a b a b^2`
- Segment `G'E` maps to `E'G` via `a b a b^(-1) a^(-1) b^(-1)`

These three transformations together form a piecewise translation that
permutes the three subsegments cyclically. The irrationality of phi
ensures the orbit of any point is infinite.

## See Also
* `IET_word`: Maps points to the corresponding generator word
* `wordForIterate`: Builds the word sequence for iterated application
-/
noncomputable def GG5_induced_IET : IntervalExchangeTransformation 3 where
  n_pos := by norm_num
  lengths := fun i =>
    if i = 0 then length1
    else if i = 1 then length2
    else length3
  lengths_pos := by
    intro i
    fin_cases i
    all_goals simp only
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

open TDCSG.CompoundSymmetry.GG5

/--
The generator word corresponding to a point's position in the IET partition.

Given a point `x` in `[0,1)`, returns the word (sequence of generators)
that encodes which interval `x` belongs to:
- If `x < length1`: returns `word1` (for segment `E'F'`)
- If `length1 <= x < length1 + length2`: returns `word2` (for segment `F'G'`)
- Otherwise: returns `word3` (for segment `G'E`)

These words correspond to the move sequences in the paper's proof:
- `word1` encodes `a^(-2) b^(-1) a^(-1) b^(-1)`
- `word2` encodes `a b a b^2`
- `word3` encodes `a b a b^(-1) a^(-1) b^(-1)`

## See Also
* `wordForIterate`: Concatenates words for multiple IET applications
-/
noncomputable def IET_word (x : Real) : Word :=
  if x < length1 then word1
  else if x < length1 + length2 then word2
  else word3

/--
The concatenated word for `k` iterations of the IET starting at `x0`.

Builds the symbolic coding of the orbit by concatenating the words
corresponding to each visited interval:
- `wordForIterate x0 0 = []` (empty word)
- `wordForIterate x0 (k+1) = wordForIterate x0 k ++ IET_word (T^k(x0))`

where `T` denotes the IET transformation `GG5_induced_IET.toFun`.

This function encodes the dynamics of the IET as a sequence of generator
words, establishing the connection between the continuous dynamics on
`[0,1)` and the discrete group structure of GG_5.

## Example
For a point `x0` that visits intervals 0, 2, 1 in three iterations:
`wordForIterate x0 3 = word1 ++ word3 ++ word2`
-/
noncomputable def wordForIterate (x0 : Real) : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate x0 n ++ IET_word (GG5_induced_IET.toFun^[n] x0)

end TDCSG.Definitions
