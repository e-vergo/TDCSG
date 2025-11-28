/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.PiecewiseIsometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Composition Definitions for Piecewise Isometries

This file contains definitions for composition and iteration of piecewise isometries.

## Main definitions

- `refinedPartitionPreimage`: The preimage-based refinement of two partitions
- `refinedPartition`: The naive refined partition (intersections)
- `PiecewiseIsometry.comp`: Composition of two piecewise isometries
- `PiecewiseIsometry.iterate`: Iteration of a piecewise isometry

-/

universe u v

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

namespace PiecewiseIsometry

/-- The refined partition obtained by intersecting pieces from two partitions with preimage.

Given partitions p (for g) and q (for f), and function g, the preimage-based refinement consists
of all nonempty intersections s ∩ g⁻¹(t) where s ∈ p and t ∈ q.
This ensures g maps each refined piece entirely into a single piece of f's partition. -/
def refinedPartitionPreimage (p q : Set (Set α)) (g : α → α) : Set (Set α) :=
  {u | ∃ s ∈ p, ∃ t ∈ q, u = s ∩ (g ⁻¹' t) ∧ (s ∩ (g ⁻¹' t)).Nonempty}

/-- The naive refined partition (kept for potential use in other contexts). -/
def refinedPartition (p q : Set (Set α)) : Set (Set α) :=
  {u | ∃ s ∈ p, ∃ t ∈ q, u = s ∩ t ∧ (s ∩ t).Nonempty}

/-- Composition of two piecewise isometries.

The composition `f.comp g` applies `g` first, then `f`. The resulting partition uses
preimage-based refinement to ensure g maps each refined piece into a single piece of
f's partition. -/
def comp [BorelSpace α] (f g : PiecewiseIsometry α) : PiecewiseIsometry α where
  partition := refinedPartitionPreimage g.partition f.partition g.toFun
  partition_measurable := sorry
  partition_countable := sorry
  partition_cover := sorry
  partition_disjoint := sorry
  partition_nonempty := by
    intro u hu
    obtain ⟨s, hs, t, ht, rfl, hnonempty⟩ := hu
    exact hnonempty
  toFun := f.toFun ∘ g.toFun
  isometry_on_pieces := sorry

/-- The nth iterate of a piecewise isometry.

`iterate f n` applies `f` a total of `n` times. By convention, `iterate f 0` is the identity. -/
def iterate [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) : ℕ → PiecewiseIsometry α
  | 0 => id
  | n + 1 => f.comp (iterate f n)

end PiecewiseIsometry
