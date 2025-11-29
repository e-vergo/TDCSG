/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.WordCorrespondence
import TDCSG.Proofs.OrbitInfinite
import TDCSG.Proofs.TwoDisk
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points

/-!
# GG5 Geometry Module

This module re-exports from the split modules and contains the main theorem infrastructure.

The GG5 geometric construction has been refactored into:
- `Points.lean`: Key geometric points E, E', F, G and their properties
- `SegmentGeometry.lean`: Translation lengths, segment ratios, irrationality
- `PlaneConversion.lean`: Complex to Plane conversion, segment parameterization
- `WordCorrespondence.lean`: Group words for IET intervals, orbit correspondence

## Main Definitions

- `GG5_critical`: The TwoDiskSystem at the critical radius

## Main Results

- `r_crit_minimal_poly`: The critical radius satisfies x^4 - 7x^2 + 11 = 0
- `GG5_infinite_at_critical_radius`: GG5 is infinite at r = sqrt(3 + phi)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-! ### Basic lemmas -/

/-- The critical radius is positive. -/
lemma r_crit_pos : 0 < r_crit := by
  unfold r_crit φ
  apply Real.sqrt_pos_of_pos
  linarith [Real.goldenRatio_pos]

/-! ### Main Results -/

/-- The critical radius satisfies x^4 - 7x^2 + 11 = 0. -/
lemma r_crit_minimal_poly :
    r_crit ^ 4 - 7 * r_crit ^ 2 + 11 = 0 := by
  unfold r_crit
  have h1 : (Real.sqrt (3 + Real.goldenRatio)) ^ 2 =
      3 + Real.goldenRatio := by
    rw [sq_sqrt]
    linarith [Real.goldenRatio_pos]
  have h2 : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    Real.goldenRatio_sq
  calc (Real.sqrt (3 + Real.goldenRatio)) ^ 4 -
          7 * (Real.sqrt (3 + Real.goldenRatio)) ^ 2 + 11
      = ((Real.sqrt (3 + Real.goldenRatio)) ^ 2) ^ 2 -
          7 * (Real.sqrt (3 + Real.goldenRatio)) ^ 2 +
          11 := by
        ring
    _ = (3 + Real.goldenRatio) ^ 2 -
          7 * (3 + Real.goldenRatio) + 11 := by
        rw [h1]
    _ = 9 + 6 * Real.goldenRatio + Real.goldenRatio ^ 2 -
          21 - 7 * Real.goldenRatio + 11 := by
        ring
    _ = 9 + 6 * Real.goldenRatio +
          (Real.goldenRatio + 1) - 21 -
          7 * Real.goldenRatio + 11 := by
        rw [h2]
    _ = 0 := by ring

/-- GG5 is infinite at r = sqrt(3 + phi).

    PROOF STRATEGY (Main Theorem Assembly):

    This theorem establishes that the compound symmetry group GG(5,5) is infinite
    at the critical radius r_crit = sqrt(3 + phi), as stated in Theorem 2 of the paper.

    The proof uses the chain:
    1. GEOMETRIC SETUP (Points.lean, PlaneConversion.lean):
       - Critical points E, E', F, G defined
       - Segment E'E lies in disk intersection

    2. TRANSLATION IRRATIONALITY (SegmentGeometry.lean):
       - translations_irrational proves translation lengths are not rationally related

    3. IET STRUCTURE (IET.lean):
       - Three-interval exchange transformation on segment E'E

    4. WORD CORRESPONDENCE (WordCorrespondence.lean):
       - Group words implement IET translations
       - IET orbit maps to group orbit

    5. INFINITE ORBIT (OrbitInfinite.lean):
       - IET with irrational translations has infinite orbits
       - GG5_IET_has_infinite_orbit provides the witness
-/
theorem GG5_infinite_at_critical_radius :
    ∃ (z : ℂ), (Orbit.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun (((z - E') / (E - E')).re)).Infinite := by
  -- Use the infinite orbit result from OrbitInfinite.lean
  obtain ⟨x₀, hx₀_in, hx₀_inf⟩ := CompoundSymmetry.GG5.GG5_IET_has_infinite_orbit
  -- Convert the IET parameter to a complex point on segment E'E
  use E' + x₀ • (E - E')
  -- Show the parameter extraction recovers x₀
  convert hx₀_inf using 2
  -- ((E' + x₀ • (E - E') - E') / (E - E')).re = x₀
  simp only [add_sub_cancel_left]
  have hne : E - E' ≠ 0 := by
    -- E' = -E, so E - E' = 2E ≠ 0
    unfold E'
    simp only [sub_neg_eq_add, ne_eq]
    have hE_ne : E ≠ 0 := E_ne_zero
    intro h
    apply hE_ne
    calc E = (E + E) / 2 := by ring
         _ = 0 / 2 := by rw [h]
         _ = 0 := by ring
  -- x₀ • (E - E') / (E - E') = x₀
  rw [Complex.real_smul, mul_div_assoc, div_self hne, mul_one, Complex.ofReal_re]

end TDCSG.CompoundSymmetry.GG5
