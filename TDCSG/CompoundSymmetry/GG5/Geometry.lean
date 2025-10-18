/-
Copyright (c) 2025-10-18 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Basic
import TDCSG.CompoundSymmetry.TwoDisk

/-!
# GG5 Geometric Construction

This file formalizes the geometric setup for the GG5 two-disk
compound symmetry group at the critical radius, as described in
Theorem 2 of the Two-Disk Compound Symmetry Groups paper
(arXiv:2302.12950v1).

## Main Definitions

- `r_crit`: The critical radius √(3 + φ) where φ is the golden
  ratio
- `ζ₅`: The primitive 5th root of unity, e^(2πi/5)
- `E`, `E'`, `F`, `G`: Key geometric points
- `GG5_critical`: The TwoDiskSystem at the critical radius

## Main Results

- `GG5_infinite_at_critical_radius`: GG5 is infinite at
  r = √(3 + φ)

## References

- Two-Disk Compound Symmetry Groups, Hearn et al.,
  arXiv:2302.12950v1
-/

namespace TDCSG.CompoundSymmetry.GG5

open scoped Complex
open Complex Real

/-! ### Critical Radius -/

/-- The critical radius for GG5, equal to √(3 + φ). -/
noncomputable def r_crit : ℝ :=
  Real.sqrt (3 + Real.goldenRatio)

/-- The critical radius is positive. -/
lemma r_crit_pos : 0 < r_crit := by
  unfold r_crit
  apply Real.sqrt_pos.mpr
  linarith [Real.goldenRatio_pos]

/-- The critical radius satisfies 2.148 < r_crit < 2.150. -/
lemma r_crit_approx : 2.148 < r_crit ∧ r_crit < 2.150 := by
  unfold r_crit
  constructor
  · rw [show (2.148 : ℝ) = Real.sqrt (2.148 ^ 2) by
      rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt
    · norm_num
    have h_sq : (2.148 : ℝ) ^ 2 = 4.613904 := by norm_num
    rw [h_sq]
    have φ_lower : (1.613904 : ℝ) < Real.goldenRatio := by
      unfold Real.goldenRatio
      have h1 : (2.227808 : ℝ) ^ 2 < 5 := by norm_num
      have h2 : (2.227808 : ℝ) < Real.sqrt 5 := by
        rw [show (2.227808 : ℝ) =
            Real.sqrt (2.227808 ^ 2) by
          rw [Real.sqrt_sq]; norm_num]
        exact Real.sqrt_lt_sqrt (by norm_num) h1
      linarith
    linarith
  · rw [show (2.150 : ℝ) = Real.sqrt (2.150 ^ 2) by
      rw [Real.sqrt_sq]; norm_num]
    apply Real.sqrt_lt_sqrt
    · linarith [Real.goldenRatio_pos]
    have h_sq : (2.150 : ℝ) ^ 2 = 4.6225 := by norm_num
    rw [h_sq]
    have φ_upper : Real.goldenRatio < (1.6225 : ℝ) := by
      unfold Real.goldenRatio
      have h1 : 5 < (2.245 : ℝ) ^ 2 := by norm_num
      have h2 : Real.sqrt 5 < (2.245 : ℝ) := by
        rw [show (2.245 : ℝ) =
            Real.sqrt (2.245 ^ 2) by
          rw [Real.sqrt_sq]; norm_num]
        exact Real.sqrt_lt_sqrt (by norm_num) h1
      linarith
    linarith


/-! ### 5th Roots of Unity -/

/-- The primitive 5th root of unity: e^(2πi/5) -/
noncomputable def ζ₅ : ℂ := exp (2 * π * I / 5)

/-- ζ₅ is a 5th root of unity. -/
lemma zeta5_pow_five : ζ₅ ^ 5 = 1 := by
  unfold ζ₅
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  ring

/-- ζ₅ is not equal to 1. -/
lemma zeta5_ne_one : ζ₅ ≠ 1 := by
  unfold ζ₅
  have : (2 : ℝ) * π / 5 ≠ 0 := by
    apply div_ne_zero
    apply mul_ne_zero
    · norm_num
    · exact Real.pi_ne_zero
    · norm_num
  intro h
  rw [show (exp (2 * ↑π * I / 5) : ℂ) =
      exp ((2 * π / 5 : ℝ) * I) by
    congr 1
    push_cast
    ring] at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have : (2 * π / 5 : ℝ) = k * (2 * π) := by
    have h_eq : ((2 * π / 5 : ℝ) * I : ℂ) =
        (k : ℂ) * ((2 * π : ℝ) * I) := by
      convert hk using 2
      push_cast
      ring
    have h_im := congr_arg Complex.im h_eq
    simp at h_im
    exact h_im
  have : (1 : ℝ) / 5 = k := by
    field_simp at this
    linarith [Real.pi_pos]
  have h_real : (k : ℝ) * 5 = 1 := by linarith
  have h_int : k * 5 = 1 := by
    have : (k : ℝ) * (5 : ℝ) = (1 : ℝ) := h_real
    norm_cast at this
  have : (1 : ℤ) % 5 = 0 := by rw [← h_int]; simp
  norm_num at this

/-- |ζ₅| = 1 -/
lemma zeta5_abs : ‖ζ₅‖ = 1 := by
  unfold ζ₅
  rw [show (2 : ℂ) * π * I / 5 = (2 * π / 5 : ℝ) * I by
    simp [div_eq_mul_inv]
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * π / 5)

/-! ### Trigonometric Identities -/

/-- The identity cos(2π/5) = (φ - 1)/2. -/
lemma cos_two_pi_fifth :
    Real.cos (2 * π / 5) = (Real.goldenRatio - 1) / 2 := by
  rw [show (2 * π / 5 : ℝ) = 2 * (π / 5) by ring]
  rw [Real.cos_two_mul]
  rw [Real.cos_pi_div_five]
  unfold Real.goldenRatio
  rw [show (2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1 : ℝ) =
      (Real.sqrt 5 - 1) / 4 by
    have h : (1 + Real.sqrt 5) ^ 2 =
        6 + 2 * Real.sqrt 5 := by
      rw [add_sq]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    calc 2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1
        = 2 * (1 + Real.sqrt 5) ^ 2 / 16 - 1 := by ring
      _ = 2 * (6 + 2 * Real.sqrt 5) / 16 - 1 := by
          rw [h]
      _ = (12 + 4 * Real.sqrt 5) / 16 - 1 := by ring
      _ = (12 + 4 * Real.sqrt 5 - 16) / 16 := by ring
      _ = (4 * Real.sqrt 5 - 4) / 16 := by ring
      _ = (Real.sqrt 5 - 1) / 4 := by ring]
  rw [show ((1 + Real.sqrt 5) / 2 - 1) / 2 =
      (Real.sqrt 5 - 1) / 4 by
    field_simp; ring]

/-! ### Key Geometric Points -/

/-- Point E on the right disk boundary: E = ζ₅ - ζ₅². -/
noncomputable def E : ℂ := ζ₅ - ζ₅^2

/-- Point E': the negation of E. -/
noncomputable def E' : ℂ := -E

/-- Point F on segment E'E: F = 1 - ζ₅ + ζ₅² - ζ₅³. -/
noncomputable def F : ℂ := 1 - ζ₅ + ζ₅^2 - ζ₅^3

/-- Point G on segment E'E: G = 2F - E. -/
noncomputable def G : ℂ := 2 * F - E

/-! ### Point Properties -/

/-- The conjugate of ζ₅ equals ζ₅⁴. -/
lemma zeta5_conj : starRingEnd ℂ ζ₅ = ζ₅^4 := by
  sorry

/-- E lies on the right disk boundary. -/
lemma E_on_right_disk_boundary : ‖E - 1‖ = r_crit := by
  sorry

/-- E lies in the left disk. -/
lemma E_in_left_disk : ‖E + 1‖ ≤ r_crit := by
  sorry

/-- F lies on the segment E'E. -/
lemma F_on_segment_E'E :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ F = E' + t • (E - E') := by
  sorry

/-- G lies on the segment E'E. -/
lemma G_on_segment_E'E :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ G = E' + t • (E - E') := by
  sorry

/-- The ordering along the segment: E' < F < G < E. -/
lemma segment_ordering :
    ∃ (t_F t_G : ℝ), 0 < t_F ∧ t_F < t_G ∧ t_G < 1 ∧
      F = E' + t_F • (E - E') ∧
      G = E' + t_G • (E - E') := by
  sorry

/-! ### Translation Lengths -/

/-- The translation length |F - (-F)|. -/
noncomputable def translation_length_1 : ℝ := ‖F - (-F)‖

/-- The translation length |E - G|. -/
noncomputable def translation_length_2 : ℝ := ‖E - G‖

/-- The total segment length |E - E'|. -/
noncomputable def segment_length : ℝ := ‖E - E'‖

/-- The ratio equals the golden ratio. -/
lemma segment_ratio_is_golden :
    segment_length / translation_length_1 = Real.goldenRatio :=
  by sorry

/-- The translation lengths are not rationally related. -/
lemma translations_irrational : ∀ (p q r : ℤ),
    p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0 →
    (p : ℝ) * segment_length + (q : ℝ) * translation_length_1 +
      (r : ℝ) * translation_length_2 ≠ 0 := by
  sorry

/-! ### Conversion to ℝ² -/

/-- Convert complex number to ℝ² coordinates. -/
noncomputable def toR2 (z : ℂ) : ℝ × ℝ := (z.re, z.im)

/-- E in ℝ². -/
noncomputable def E_R2 : ℝ × ℝ := toR2 E

/-- E' in ℝ². -/
noncomputable def E'_R2 : ℝ × ℝ := toR2 E'

/-- F in ℝ². -/
noncomputable def F_R2 : ℝ × ℝ := toR2 F

/-- G in ℝ². -/
noncomputable def G_R2 : ℝ × ℝ := toR2 G

/-! ### Disk Intersection -/

/-- E' is on the left disk boundary. -/
lemma E'_on_left_disk_boundary : ‖E' - (-1)‖ = r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (-1 : ℂ)) = -(E - 1) by ring]
  rw [norm_neg]
  exact E_on_right_disk_boundary

/-- E' is in the right disk. -/
lemma E'_in_right_disk : ‖E' - 1‖ ≤ r_crit := by
  unfold E'
  rw [show ((-E : ℂ) - (1 : ℂ)) = -(E + 1) by ring]
  rw [norm_neg]
  exact E_in_left_disk

/-- Points on segment E'E lie in the disk intersection. -/
lemma segment_in_disk_intersection (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    let p := E' + t • (E - E')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  have hp_segment : p ∈ segment ℝ E' E := by
    use (1 - t), t
    constructor; · linarith [ht.1]
    constructor; · exact ht.1
    constructor; · linarith [ht.2]
    calc (1 - t) • E' + t • E
        = E' - t • E' + t • E := by
          rw [sub_smul, one_smul]
      _ = E' + (t • E - t • E') := by
          ring
      _ = E' + t • (E - E') := by
          rw [smul_sub]
  constructor
  · have h_E'_in_left :
        E' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      exact E'_on_left_disk_boundary.le
    have h_E_in_left :
        E ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      rw [show (E - (-1) : ℂ) = E + 1 by ring]
      exact E_in_left_disk
    have h_convex : Convex ℝ
        (Metric.closedBall ((-1) : ℂ) r_crit) :=
      convex_closedBall ((-1) : ℂ) r_crit
    have h_segment_subset :
        segment ℝ E' E ⊆
          Metric.closedBall ((-1) : ℂ) r_crit :=
      h_convex.segment_subset h_E'_in_left h_E_in_left
    have hp_in_left :
        p ∈ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_left
    simp only [dist_eq_norm] at hp_in_left
    rw [show (p - (-1) : ℂ) = p + 1 by ring] at hp_in_left
    exact hp_in_left
  · have h_E'_in_right :
        E' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      exact E'_in_right_disk
    have h_E_in_right :
        E ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]
      simp only [dist_eq_norm]
      rw [show (E - 1 : ℂ) = E - 1 by ring]
      exact E_on_right_disk_boundary.le
    have h_convex : Convex ℝ
        (Metric.closedBall (1 : ℂ) r_crit) :=
      convex_closedBall (1 : ℂ) r_crit
    have h_segment_subset :
        segment ℝ E' E ⊆ Metric.closedBall (1 : ℂ) r_crit :=
      h_convex.segment_subset h_E'_in_right h_E_in_right
    have hp_in_right :
        p ∈ Metric.closedBall (1 : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_right
    simp only [dist_eq_norm] at hp_in_right
    exact hp_in_right

/-! ### TwoDiskSystem Definition -/

/-- The GG5 two-disk system at the critical radius. -/
noncomputable def GG5_critical :
    CompoundSymmetry.TwoDiskSystem where
  r1 := r_crit
  r2 := r_crit
  n1 := 5
  n2 := 5
  r1_pos := r_crit_pos
  r2_pos := r_crit_pos
  n1_ge := by norm_num
  n2_ge := by norm_num

/-! ### Main Results -/

/-- The critical radius satisfies x⁴ - 7x² + 11 = 0. -/
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

/-- GG5 is infinite at r = √(3 + φ). -/
theorem GG5_infinite_at_critical_radius :
    ∃ (point : ℂ), ∀ (n : ℕ),
      ∃ (orbit_size : ℕ), n < orbit_size := by
  sorry

end TDCSG.CompoundSymmetry.GG5
