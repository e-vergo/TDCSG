/-
Copyright (c) 2025-10-18 TDCSG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDCSG Contributors
-/

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TDCSG.Rotations
import TDCSG.Definitions.Geometry

/-!
# Planar Disk Theorems

This file contains theorems about planar disks (closed balls in ℝ²)
for the TDCSG formalization.

The `Disk` definition is in `TDCSG.Definitions.Geometry`.

## Main Results

* `disks_overlap_iff`: Characterization of when two disks overlap.
* `disk_inter_measurable`: The intersection of two disks is measurable.
* `disk_inter_compact`: The intersection of two disks is compact.

## References

* Two-Disk Compound Symmetry Groups paper (arXiv:2302.12950v1)
-/

open Metric Set MeasureTheory
open scoped Topology

namespace TDCSG

-- Import the ℝ² notation from Planar namespace
open Planar

-- Disk definition imported from TDCSG.Definitions.Geometry
open TDCSG.Definitions

namespace Disk

variable {c₁ c₂ : ℝ²} {r₁ r₂ : ℝ}

/-- Two disks overlap if and only if the distance between their centers
is at most the sum of their radii. -/
lemma disks_overlap_iff (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    (Disk c₁ r₁ ∩ Disk c₂ r₂).Nonempty ↔ dist c₁ c₂ ≤ r₁ + r₂ := by
  unfold Disk
  constructor
  · intro ⟨x, hx⟩
    simp only [mem_inter_iff, mem_closedBall] at hx
    have h1 : dist c₁ x ≤ r₁ := by rw [dist_comm]; exact hx.1
    have h2 : dist x c₂ ≤ r₂ := hx.2
    calc dist c₁ c₂ ≤ dist c₁ x + dist x c₂ := dist_triangle c₁ x c₂
      _ ≤ r₁ + r₂ := add_le_add h1 h2
  · intro h_dist
    by_cases h_eq : c₁ = c₂
    · subst h_eq
      use c₁
      simp [mem_closedBall, hr₁, hr₂]
    · -- Construct witness point on line from c₁ toward c₂
      have h_dist_pos : 0 < dist c₁ c₂ := dist_pos.mpr h_eq
      set d := dist c₁ c₂
      -- Use parameter t ∈ [0,1] to parametrize the line segment
      -- Choose t such that distance from c₁ is min(r₁, d)
      by_cases h_case : r₁ ≤ d
      · -- Standard case: r₁ ≤ d, use point at distance r₁ from c₁
        set t := r₁ / d
        set x := c₁ + t • (c₂ - c₁)
        use x
        simp only [mem_inter_iff, mem_closedBall]
        constructor
        · -- Show dist x c₁ ≤ r₁
          show dist x c₁ ≤ r₁
          have : dist x c₁ = r₁ := by
            calc dist x c₁ = ‖x - c₁‖ := by rw [dist_eq_norm]
              _ = ‖c₁ + t • (c₂ - c₁) - c₁‖ := rfl
              _ = ‖t • (c₂ - c₁)‖ := by rw [add_sub_cancel_left]
              _ = t * ‖c₂ - c₁‖ := by
                    rw [norm_smul, Real.norm_of_nonneg
                      (div_nonneg hr₁ (le_of_lt h_dist_pos))]
              _ = t * d := by rw [← dist_eq_norm, dist_comm]
              _ = r₁ := div_mul_cancel₀ r₁ (ne_of_gt h_dist_pos)
          linarith
        · -- Show dist x c₂ ≤ r₂
          have key : x - c₂ = (1 - t) • (c₁ - c₂) := by
            calc x - c₂ = c₁ + t • (c₂ - c₁) - c₂ := rfl
              _ = c₁ - c₂ + t • (c₂ - c₁) := by abel
              _ = c₁ - c₂ + t • c₂ - t • c₁ := by rw [smul_sub]; abel
              _ = (1 - t) • c₁ - (1 - t) • c₂ := by
                    rw [sub_smul, sub_smul, one_smul, one_smul]
                    abel
              _ = (1 - t) • (c₁ - c₂) := by rw [smul_sub]
          show dist x c₂ ≤ r₂
          have h_t_le_1 : t ≤ 1 := by
            rw [div_le_one h_dist_pos]
            exact h_case
          have h_sub_nonneg : 0 ≤ 1 - t := by linarith
          have h_td_eq_r1 : t * d = r₁ :=
            div_mul_cancel₀ r₁ (ne_of_gt h_dist_pos)
          calc dist x c₂ = ‖x - c₂‖ := by rw [dist_eq_norm]
            _ = ‖(1 - t) • (c₁ - c₂)‖ := by rw [key]
            _ = |1 - t| * ‖c₁ - c₂‖ := norm_smul _ _
            _ = (1 - t) * ‖c₁ - c₂‖ := by rw [abs_of_nonneg h_sub_nonneg]
            _ = (1 - t) * d := by rw [← dist_eq_norm]
            _ = d - r₁ := by linarith [h_td_eq_r1]
            _ ≤ r₂ := by linarith [h_dist]
      · -- Case r₁ > d: any point in the first ball works (use c₂)
        push_neg at h_case
        use c₂
        simp only [mem_inter_iff, mem_closedBall]
        constructor
        · show dist c₂ c₁ ≤ r₁
          have : dist c₂ c₁ < r₁ := by
            calc dist c₂ c₁ = d := by rw [dist_comm]
              _ < r₁ := h_case
          linarith
        · show dist c₂ c₂ ≤ r₂
          simp [dist_self, hr₂]

/-- The intersection of two disks is measurable with respect to the
Borel σ-algebra. -/
lemma disk_inter_measurable (c₁ c₂ : ℝ²) (r₁ r₂ : ℝ) :
    MeasurableSet (Disk c₁ r₁ ∩ Disk c₂ r₂) := by
  unfold Disk
  exact MeasurableSet.inter isClosed_closedBall.measurableSet
    isClosed_closedBall.measurableSet

/-- The intersection of two disks is compact. -/
lemma disk_inter_compact (c₁ c₂ : ℝ²) (r₁ r₂ : ℝ) :
    IsCompact (Disk c₁ r₁ ∩ Disk c₂ r₂) := by
  unfold Disk
  exact IsCompact.inter (isCompact_closedBall c₁ r₁)
    (isCompact_closedBall c₂ r₂)

end Disk

end TDCSG
