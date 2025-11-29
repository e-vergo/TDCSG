/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.PiecewiseIsometry
import TDCSG.Proofs.Composition
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measure-Preserving Piecewise Isometry Definitions

This file contains the core definitions for measure-preserving piecewise isometries.

## Main definitions

- `MeasurePreservingPiecewiseIsometry`: A piecewise isometry that preserves a given measure
- `IsInvariant`: A set is forward-invariant under the map
- `IsCompletelyInvariant`: A set is mapped onto itself bijectively
- `idMeasurePreserving`: The identity as a measure-preserving piecewise isometry
- `compMP`: Composition of measure-preserving piecewise isometries
- `iterateMP`: Iteration of a measure-preserving piecewise isometry
- `toPiecewiseIsometry_of_measurePreserving`: Constructor from a piecewise isometry

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

/-- A measure-preserving piecewise isometry.

This structure extends `PiecewiseIsometry` by requiring that the underlying function is
measurable and preserves a specified measure `μ`. -/
structure MeasurePreservingPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends PiecewiseIsometry α where
  /-- The underlying function is measurable -/
  measurable_toFun : Measurable toFun
  /-- The function preserves the measure μ -/
  measure_preserving : MeasureTheory.MeasurePreserving toFun μ μ

namespace MeasurePreservingPiecewiseIsometry

variable {μ : MeasureTheory.Measure α}

/-- Allow function application notation. -/
instance : CoeFun (MeasurePreservingPiecewiseIsometry α μ) (fun _ => α → α) where
  coe f := f.toFun

/-- A set is forward-invariant if it is mapped into itself. -/
def IsInvariant (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) : Prop :=
  f.toFun '' s ⊆ s

/-- A set is completely invariant if it is mapped onto itself bijectively. -/
def IsCompletelyInvariant (f : MeasurePreservingPiecewiseIsometry α μ) (s : Set α) : Prop :=
  f.toFun '' s = s

/-- Construct a measure-preserving piecewise isometry from a piecewise isometry with
additional properties. -/
def toPiecewiseIsometry_of_measurePreserving (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_mp : MeasureTheory.MeasurePreserving f.toFun μ μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f
  measurable_toFun := h_meas
  measure_preserving := h_mp

/-- The identity as a measure-preserving piecewise isometry. -/
def idMeasurePreserving [Nonempty α] : MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := PiecewiseIsometry.id
  measurable_toFun := measurable_id
  measure_preserving := MeasureTheory.MeasurePreserving.id μ

/-- Composition of measure-preserving piecewise isometries preserves measure. -/
def compMP [OpensMeasurableSpace α] [BorelSpace α] (f g : MeasurePreservingPiecewiseIsometry α μ) :
    MeasurePreservingPiecewiseIsometry α μ where
  toPiecewiseIsometry := f.toPiecewiseIsometry.comp g.toPiecewiseIsometry
  measurable_toFun := f.measurable_toFun.comp g.measurable_toFun
  measure_preserving := f.measure_preserving.comp g.measure_preserving

/-- The nth iterate of a measure-preserving piecewise isometry. -/
def iterateMP [Nonempty α] [OpensMeasurableSpace α] [BorelSpace α]
    (f : MeasurePreservingPiecewiseIsometry α μ) : ℕ → MeasurePreservingPiecewiseIsometry α μ
  | 0 => idMeasurePreserving
  | n + 1 => compMP f (iterateMP f n)

end MeasurePreservingPiecewiseIsometry

end PiecewiseIsometry
