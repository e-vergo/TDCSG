/-
Copyright (c) 2025 TDCSG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDCSG Contributors
-/

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TDCSG.Planar.Rotations

/-!
# Planar Disks

This file defines planar disks (closed balls in ℝ²) and establishes their key properties
for the TDCSG formalization.

## Main Definitions

* `Disk`: A closed disk in ℝ² defined as a closed ball in the metric space.

## Main Results

* `disks_overlap_iff`: Characterization of when two disks overlap.
* `disk_inter_measurable`: The intersection of two disks is measurable.
* `disk_inter_compact`: The intersection of two disks is compact.

## Implementation Notes

We define disks as closed balls to ensure:
- Compactness (closed and bounded in ℝ²)
- Measurability under the Borel σ-algebra
- Compatibility with standard metric space theory

The definition uses `Metric.closedBall` from Mathlib's metric space library.

## References

* Two-Disk Compound Symmetry Groups paper (arXiv:2302.12950v1)
-/

open Metric Set MeasureTheory
open scoped Topology

namespace TDCSG

-- Import the ℝ² notation from Planar namespace
open Planar

/-- A disk in ℝ² is a closed ball with specified center and radius.

This is defined as a simple type alias to `Set ℝ²` for the closed ball,
providing a lightweight wrapper around `Metric.closedBall`. -/
def Disk (center : ℝ²) (radius : ℝ) : Set ℝ² := Metric.closedBall center radius

namespace Disk

variable {c₁ c₂ : ℝ²} {r₁ r₂ : ℝ}

/--
Two disks overlap if and only if the distance between their centers
is at most the sum of their radii.

This is a fundamental geometric characterization used throughout
the TDCSG development.
-/
lemma disks_overlap_iff (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    (Disk c₁ r₁ ∩ Disk c₂ r₂).Nonempty ↔ dist c₁ c₂ ≤ r₁ + r₂ := by
  sorry

/--
The intersection of two disks is measurable with respect to the Borel σ-algebra.

This follows from the measurability of closed balls in metric spaces.
-/
lemma disk_inter_measurable (c₁ c₂ : ℝ²) (r₁ r₂ : ℝ) :
    MeasurableSet (Disk c₁ r₁ ∩ Disk c₂ r₂) := by
  sorry

/--
The intersection of two disks is compact.

This is a consequence of the intersection of two compact sets being compact,
combined with the fact that closed balls in ℝ² are compact.
-/
lemma disk_inter_compact (c₁ c₂ : ℝ²) (r₁ r₂ : ℝ) :
    IsCompact (Disk c₁ r₁ ∩ Disk c₂ r₂) := by
  sorry

end Disk

end TDCSG
