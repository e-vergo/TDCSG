/-
Copyright (c) 2025-11-22 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Definitions.Orbit
import TDCSG.Definitions.IET
import TDCSG.Proofs.Orbit
import TDCSG.Proofs.IET
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Function

/-!
# Infinite Orbits in GG(5,5) Interval Exchange Transformation

This file establishes foundational infrastructure for proving that the interval
exchange transformation emerging from the GG(5,5) compound symmetry system
has infinite orbits.

The fundamental IET definitions (length1, length2, length3, displacements)
are in TDCSG.Definitions.IET.

## Main results

* `goldenRatio_mul_rat_irrational`: Golden ratio times any nonzero rational is irrational
* `GG5_IET_rotation_irrational`: The GG5 IET rotation ratio length2/length1 = φ is irrational
* `orbitSet`: Definition of the orbit set of a point
* `finite_orbit_implies_periodic`: If an orbit set is finite, the point is eventually periodic
* `orbit_unbounded_of_injective_pieces`: For isometries on disjoint pieces, certain orbits are unbounded

## Mathematical Background

The GG5 IET has interval lengths in golden ratio proportions:
- length1 = 1/(1 + φ + φ²)
- length2 = φ/(1 + φ + φ²)
- length3 = φ²/(1 + φ + φ²)

Therefore length2/length1 = φ, which is irrational.

For IETs with irrational rotation ratios, a deep theorem (Keane 1975, Veech/Masur 1980s)
states that all orbits are dense, hence infinite and non-periodic. The complete proof
requires substantial ergodic theory machinery.

We establish the infrastructure and prove what we can rigorously, documenting the gap.

## Implementation Notes

This file provides:
1. Complete proofs of irrationality properties
2. Definitions and basic lemmas about orbits
3. Infrastructure for future completion of the main theorem

The statement "IETs with irrational rotation → no periodic orbits" requires deep
measure-theoretic arguments beyond current Mathlib ergodic theory coverage.

-/

namespace TDCSG.CompoundSymmetry.GG5

open Real Function Set Orbit TDCSG.Definitions

/-! ### Irrationality results -/

/-- The golden ratio times any nonzero rational is irrational. -/
theorem goldenRatio_mul_rat_irrational (q : ℚ) (hq : q ≠ 0) :
    Irrational (goldenRatio * q) := by
  intro ⟨r, hr⟩
  have h_phi_irr := goldenRatio_irrational
  apply h_phi_irr
  use r / q
  have hq_cast : (q : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hq
  rw [Rat.cast_div, div_eq_iff hq_cast, ← hr]

/-- The GG5 IET rotation ratio is irrational.
    Since length2 = φ * length1, we have length2/length1 = φ. -/
theorem GG5_IET_rotation_irrational :
    Irrational (length2 / length1) := by
  have h_rel := interval_lengths_golden_ratio_relations.1
  rw [h_rel]
  have h1_pos := length1_pos
  have h1_ne : length1 ≠ 0 := ne_of_gt h1_pos
  rw [mul_div_assoc, div_self h1_ne, mul_one]
  exact goldenRatio_irrational

/-! ### Main theorems -/

/-- The orbit contains at least one point (the starting point itself). -/
theorem GG5_IET_orbit_nonempty (x : ℝ) (_ : x ∈ Ico 0 1) :
    (Orbit.orbitSet GG5_induced_IET.toFun x).Nonempty :=
  ⟨x, Orbit.mem_orbitSet_self _ _⟩

/-- For any n, we can construct a finite set of orbit points.
    This provides infrastructure for ergodic theory analysis. -/
theorem GG5_IET_orbit_finite_subset (n : ℕ) :
    ∃ (x : ℝ), x ∈ Ico 0 1 ∧
      ∃ (pts : Finset ℝ), pts.Nonempty ∧
        (∀ y ∈ pts, y ∈ Orbit.orbitSet GG5_induced_IET.toFun x) := by
  use length1 / 2
  constructor
  · constructor
    · have : 0 < length1 := length1_pos
      linarith
    · calc length1 / 2 < length1 := by linarith [length1_pos]
        _ < 1 := by
          have : length1 + length2 + length3 = 1 := lengths_sum_to_one
          linarith [length2_pos, length3_pos]
  · -- Construct orbit points from first n iterates
    use Finset.image (fun k : Fin (n+1) => (GG5_induced_IET.toFun^[k.val]) (length1 / 2)) Finset.univ
    constructor
    · -- Nonempty because we include at least f^[0] x = x
      use (GG5_induced_IET.toFun^[0]) (length1 / 2)
      simp [Finset.mem_image]
      use ⟨0, by omega⟩
      simp
    · intro y hy
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hy
      rw [← hk]
      exact Orbit.orbitSet_iterate _ _ _

/-- Main infrastructure theorem: The GG5 IET has points with nonempty orbit segments.

    This theorem establishes ergodic theory infrastructure by showing we can
    construct finite orbit segments for any point in the domain.

    **Note**: The full theorem "orbits are infinite" requires proving that IETs with
    irrational rotation ratios have no periodic orbits (Keane 1975). That deep result
    would immediately imply orbit sets are infinite via `Orbit.finite_orbit_implies_periodic`.
    The infrastructure here supports future completion of that proof.

    We have proven:
    - The rotation ratio length2/length1 = φ is irrational
    - Finite orbits imply eventual periodicity
    - The logical framework connecting these

    The remaining gap is the deep ergodic theory result connecting irrational
    rotation to non-periodicity in IETs. -/
theorem GG5_IET_has_orbit_structure :
    ∀ (_ : ℕ), ∃ (x : ℝ) (_ : x ∈ Ico 0 1) (pts : Finset ℝ),
      pts.Nonempty ∧ (∀ y ∈ pts, y ∈ Orbit.orbitSet GG5_induced_IET.toFun x) := by
  intro n
  obtain ⟨x, hx, pts, h_ne, h_in⟩ := GG5_IET_orbit_finite_subset n
  exact ⟨x, hx, pts, h_ne, h_in⟩

/-! ### GG5-Specific No Periodic Orbits Theorem -/

/-! #### Displacement computations for GG5 IET

The GG5 IET has permutation `swap 0 2`, meaning:
- Interval 0 maps to position 2
- Interval 1 stays at position 1
- Interval 2 maps to position 0

The displacement for a point x in interval i is:
  f(x) - x = rangeLeft(permutation i) - domainLeft i

Computing explicitly:
- d₀ = rangeLeft 2 - domainLeft 0 = (length3 + length2) - 0 = 1 - length1
- d₁ = rangeLeft 1 - domainLeft 1 = length3 - length1
- d₂ = rangeLeft 0 - domainLeft 2 = 0 - (length1 + length2) = -1/2

In terms of φ where 1 + φ + φ² = 2(1+φ):
- d₀ = (1 + 2φ)/(2(1+φ))
- d₁ = φ/(2(1+φ))
- d₂ = -(1+φ)/(2(1+φ))

The displacements are defined in TDCSG.Definitions.IET.
-/

/-- GG5 domain boundaries -/
theorem GG5_domainLeft_0 : GG5_induced_IET.domainLeft 0 = 0 := by
  unfold IntervalExchangeTransformation.domainLeft
  simp

theorem GG5_domainLeft_1 : GG5_induced_IET.domainLeft 1 = length1 := by
  unfold IntervalExchangeTransformation.domainLeft GG5_induced_IET
  simp

theorem GG5_domainLeft_2 : GG5_induced_IET.domainLeft 2 = length1 + length2 := by
  unfold IntervalExchangeTransformation.domainLeft GG5_induced_IET
  simp [Fin.sum_univ_two]

/-- GG5 range boundaries (accounting for permutation swap 0 2) -/
theorem GG5_rangeLeft_0 : GG5_induced_IET.rangeLeft 0 = 0 := by
  unfold IntervalExchangeTransformation.rangeLeft
  simp

theorem GG5_rangeLeft_1 : GG5_induced_IET.rangeLeft 1 = length3 := by
  unfold IntervalExchangeTransformation.rangeLeft GG5_induced_IET
  simp

theorem GG5_rangeLeft_2 : GG5_induced_IET.rangeLeft 2 = length3 + length2 := by
  unfold IntervalExchangeTransformation.rangeLeft GG5_induced_IET
  simp [Fin.sum_univ_two, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left]

/-- GG5 permutation values -/
@[simp] theorem GG5_perm_0 : GG5_induced_IET.permutation 0 = 2 := rfl

@[simp] theorem GG5_perm_1 : GG5_induced_IET.permutation 1 = 1 := rfl

@[simp] theorem GG5_perm_2 : GG5_induced_IET.permutation 2 = 0 := rfl

/-- The actual displacement for interval 0 matches displacement0 -/
theorem GG5_actual_displacement_interval0 :
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) - GG5_induced_IET.domainLeft 0 = displacement0 := by
  simp only [GG5_perm_0, GG5_rangeLeft_2, GG5_domainLeft_0]
  unfold displacement0
  have h := lengths_sum_to_one
  linarith

/-- The actual displacement for interval 1 matches displacement1 -/
theorem GG5_actual_displacement_interval1 :
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 1) - GG5_induced_IET.domainLeft 1 = displacement1 := by
  simp only [GG5_perm_1, GG5_rangeLeft_1, GG5_domainLeft_1]
  unfold displacement1
  ring

/-- The actual displacement for interval 2 matches displacement2 -/
theorem GG5_actual_displacement_interval2 :
    GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 2) - GG5_induced_IET.domainLeft 2 = displacement2 := by
  simp only [GG5_perm_2, GG5_rangeLeft_0, GG5_domainLeft_2]
  unfold displacement2
  -- length1 + length2 = 1/2, so 0 - (length1 + length2) = -1/2
  have h_sq : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq
  have h_denom : 1 + goldenRatio + goldenRatio ^ 2 = 2 * (1 + goldenRatio) := by rw [h_sq]; ring
  unfold length1 length2
  rw [h_denom]
  have h_pos : 0 < 1 + goldenRatio := by have := goldenRatio_pos; linarith
  field_simp
  ring

/-- The displacement function equals f(x) - x for any x in [0,1). -/
theorem GG5_displacement_eq_toFun_sub (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    GG5_displacement x = GG5_induced_IET.toFun x - x := by
  unfold GG5_displacement
  -- Case analysis on which interval x is in
  by_cases h0 : x < length1
  · -- x in interval 0: [0, length1)
    simp only [h0, if_true]
    -- Need to compute GG5_induced_IET.toFun x for x in interval 0
    unfold IntervalExchangeTransformation.toFun
    have h_in_0 : x ∈ GG5_induced_IET.interval 0 := by
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
      rw [GG5_domainLeft_0]
      simp only [GG5_induced_IET, Set.mem_Ico]
      constructor
      · exact hx.1
      · simp; exact h0
    -- The epsilon chooses output for interval 0
    have h_ex : ∃ y, ∃ i, x ∈ GG5_induced_IET.interval i ∧
        y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i) := by
      use GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) + (x - GG5_induced_IET.domainLeft 0), 0

    have h_unique : ∀ y, (∃ i, x ∈ GG5_induced_IET.interval i ∧
        y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i)) →
        y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) + (x - GG5_induced_IET.domainLeft 0) := by
      intro y ⟨i, hi_mem, hi_eq⟩
      have : i = 0 := by
        by_contra h_ne
        have h_disj := GG5_induced_IET.intervals_disjoint (Set.mem_range_self 0) (Set.mem_range_self i)
                         (by intro heq; exact h_ne (GG5_induced_IET.interval_injective heq).symm)
        have : x ∈ GG5_induced_IET.interval 0 ∩ GG5_induced_IET.interval i := ⟨h_in_0, hi_mem⟩
        exact Set.disjoint_iff_inter_eq_empty.mp h_disj |>.subset this
      rw [this] at hi_eq
      exact hi_eq
    -- Apply epsilon_eq_of_forall
    have h_eps : Classical.epsilon (fun y => ∃ i, x ∈ GG5_induced_IET.interval i ∧
        y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i)) =
        GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) + (x - GG5_induced_IET.domainLeft 0) := by
      have h_spec := Classical.epsilon_spec h_ex
      exact h_unique _ h_spec
    rw [h_eps, GG5_domainLeft_0]
    -- Goal: displacement0 = rangeLeft (permutation 0) + (x - 0) - x
    -- Simplify x - 0 - x = 0, then use GG5_actual_displacement_interval0
    have h_simp : GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) + (x - 0) - x =
                  GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 0) := by ring
    rw [h_simp]
    -- Now goal: displacement0 = rangeLeft (permutation 0)
    have h := GG5_actual_displacement_interval0
    simp only [GG5_domainLeft_0, sub_zero] at h
    exact h.symm
  · by_cases h1 : x < length1 + length2
    · -- x in interval 1: [length1, length1 + length2)
      simp only [h0, h1, if_false, if_true]
      unfold IntervalExchangeTransformation.toFun
      have h_in_1 : x ∈ GG5_induced_IET.interval 1 := by
        unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
        rw [GG5_domainLeft_1]
        simp only [GG5_induced_IET, Set.mem_Ico]
        constructor
        · push_neg at h0; exact h0
        · simp; exact h1
      have h_ex : ∃ y, ∃ i, x ∈ GG5_induced_IET.interval i ∧
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i) := by
        use GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 1) + (x - GG5_induced_IET.domainLeft 1), 1

      have h_unique : ∀ y, (∃ i, x ∈ GG5_induced_IET.interval i ∧
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i)) →
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 1) + (x - GG5_induced_IET.domainLeft 1) := by
        intro y ⟨i, hi_mem, hi_eq⟩
        have : i = 1 := by
          by_contra h_ne
          have h_disj := GG5_induced_IET.intervals_disjoint (Set.mem_range_self 1) (Set.mem_range_self i)
                           (by intro heq; exact h_ne (GG5_induced_IET.interval_injective heq).symm)
          have : x ∈ GG5_induced_IET.interval 1 ∩ GG5_induced_IET.interval i := ⟨h_in_1, hi_mem⟩
          exact Set.disjoint_iff_inter_eq_empty.mp h_disj |>.subset this
        rw [this] at hi_eq
        exact hi_eq
      have h_eps : Classical.epsilon (fun y => ∃ i, x ∈ GG5_induced_IET.interval i ∧
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i)) =
          GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 1) + (x - GG5_induced_IET.domainLeft 1) := by
        have h_spec := Classical.epsilon_spec h_ex
        exact h_unique _ h_spec
      rw [h_eps, GG5_domainLeft_1]
      rw [← GG5_actual_displacement_interval1, GG5_domainLeft_1]
      ring
    · -- x in interval 2: [length1 + length2, 1)
      simp only [h0, h1, if_false]
      unfold IntervalExchangeTransformation.toFun
      have h_in_2 : x ∈ GG5_induced_IET.interval 2 := by
        unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight
        rw [GG5_domainLeft_2]
        simp only [GG5_induced_IET, Set.mem_Ico]
        constructor
        · push_neg at h1; exact h1
        · have h_sum := lengths_sum_to_one
          simp
          linarith [hx.2]
      have h_ex : ∃ y, ∃ i, x ∈ GG5_induced_IET.interval i ∧
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i) := by
        use GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 2) + (x - GG5_induced_IET.domainLeft 2), 2
      have h_unique : ∀ y, (∃ i, x ∈ GG5_induced_IET.interval i ∧
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i)) →
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 2) + (x - GG5_induced_IET.domainLeft 2) := by
        intro y ⟨i, hi_mem, hi_eq⟩
        have : i = 2 := by
          by_contra h_ne
          have h_disj := GG5_induced_IET.intervals_disjoint (Set.mem_range_self 2) (Set.mem_range_self i)
                           (by intro heq; exact h_ne (GG5_induced_IET.interval_injective heq).symm)
          have : x ∈ GG5_induced_IET.interval 2 ∩ GG5_induced_IET.interval i := ⟨h_in_2, hi_mem⟩
          exact Set.disjoint_iff_inter_eq_empty.mp h_disj |>.subset this
        rw [this] at hi_eq
        exact hi_eq
      have h_eps : Classical.epsilon (fun y => ∃ i, x ∈ GG5_induced_IET.interval i ∧
          y = GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) + (x - GG5_induced_IET.domainLeft i)) =
          GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation 2) + (x - GG5_induced_IET.domainLeft 2) := by
        have h_spec := Classical.epsilon_spec h_ex
        exact h_unique _ h_spec
      rw [h_eps, GG5_domainLeft_2]
      rw [← GG5_actual_displacement_interval2, GG5_domainLeft_2]
      ring

/-- For a point y in [0,1), the cumulative displacement over n iterations
    equals f^[n](y) - y, using telescope sum. -/
theorem cumulative_displacement_telescope (y : ℝ)
    (n : ℕ) (hn : ∀ k < n, (GG5_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1) :
    cumulative_displacement y n = (GG5_induced_IET.toFun^[n]) y - y := by
  induction n with
  | zero =>
    simp [cumulative_displacement]
  | succ k ih =>
    rw [cumulative_displacement, Finset.sum_range_succ]
    have hk : ∀ j < k, (GG5_induced_IET.toFun^[j]) y ∈ Set.Ico 0 1 := by
      intro j hj; exact hn j (Nat.lt_trans hj (Nat.lt_succ_self k))
    have h_fk_mem : (GG5_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1 := hn k (Nat.lt_succ_self k)
    rw [GG5_displacement_eq_toFun_sub _ h_fk_mem]
    simp only [cumulative_displacement] at ih
    rw [ih hk]
    simp only [Function.iterate_succ_apply']
    ring

/-- If a + b*φ = 0 for integers a, b, then a = b = 0.
    This is the linear independence of {1, φ} over ℤ. -/
theorem int_add_int_mul_phi_eq_zero (a b : ℤ)
    (h : (a : ℝ) + (b : ℝ) * goldenRatio = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · -- If b = 0, then a = 0 follows from h
    simp only [hb, Int.cast_zero, zero_mul, add_zero] at h
    have ha : a = 0 := by
      have : (a : ℝ) = 0 := h
      exact Int.cast_eq_zero.mp this
    exact ⟨ha, hb⟩
  · -- If b ≠ 0, derive contradiction from irrationality
    exfalso
    have hφ : goldenRatio = -(a : ℝ) / b := by
      have hb_ne : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
      field_simp at h ⊢
      linarith
    -- goldenRatio equals a rational, contradicting irrationality
    have : Irrational goldenRatio := goldenRatio_irrational
    apply this
    use ((-a : ℤ) : ℚ) / b
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    push_cast
    exact hφ.symm

/-- Key algebraic lemma: For any natural numbers n₀, n₁, n₂ with sum > 0,
    the weighted displacement sum n₀*d₀ + n₁*d₁ + n₂*d₂ ≠ 0.

    This is the core constraint that prevents periodic orbits in the GG5 IET. -/
theorem displacement_sum_ne_zero (n₀ n₁ n₂ : ℕ) (h_sum : 0 < n₀ + n₁ + n₂) :
    n₀ * displacement0 + n₁ * displacement1 + n₂ * displacement2 ≠ 0 := by
  intro h_zero
  -- Express in terms of φ
  have h_denom_pos : 0 < 2 * (1 + goldenRatio) := by
    have : 0 < goldenRatio := goldenRatio_pos
    linarith
  have h_denom_ne : 2 * (1 + goldenRatio) ≠ 0 := ne_of_gt h_denom_pos
  -- Rewrite using the displacement formulas
  rw [displacement0_formula, displacement1_formula, displacement2_formula] at h_zero
  -- The equation is:
  -- n₀ * (1 + 2φ)/(2(1+φ)) + n₁ * φ/(2(1+φ)) + n₂ * (-(1+φ))/(2(1+φ)) = 0
  -- Multiply by 2(1+φ) to clear denominators:
  -- n₀(1 + 2φ) + n₁φ - n₂(1+φ) = 0
  have h_clear : (n₀ : ℝ) * (1 + 2 * goldenRatio) + (n₁ : ℝ) * goldenRatio -
                 (n₂ : ℝ) * (1 + goldenRatio) = 0 := by
    have h_eq := h_zero
    have h1 : (n₀ : ℝ) * ((1 + 2 * goldenRatio) / (2 * (1 + goldenRatio))) =
              (n₀ : ℝ) * (1 + 2 * goldenRatio) / (2 * (1 + goldenRatio)) := by ring
    have h2 : (n₁ : ℝ) * (goldenRatio / (2 * (1 + goldenRatio))) =
              (n₁ : ℝ) * goldenRatio / (2 * (1 + goldenRatio)) := by ring
    have h3 : (n₂ : ℝ) * (-(1 + goldenRatio) / (2 * (1 + goldenRatio))) =
              -(n₂ : ℝ) * (1 + goldenRatio) / (2 * (1 + goldenRatio)) := by ring
    rw [h1, h2, h3] at h_eq
    have h_combined : ((n₀ : ℝ) * (1 + 2 * goldenRatio) + (n₁ : ℝ) * goldenRatio -
                      (n₂ : ℝ) * (1 + goldenRatio)) / (2 * (1 + goldenRatio)) = 0 := by
      field_simp at h_eq ⊢
      linarith
    exact div_eq_zero_iff.mp h_combined |>.resolve_right h_denom_ne
  -- Expand: n₀ + 2n₀φ + n₁φ - n₂ - n₂φ = 0
  -- Group by 1 and φ: (n₀ - n₂) + (2n₀ + n₁ - n₂)φ = 0
  have h_coeff : (n₀ : ℝ) - n₂ + ((2 : ℝ) * n₀ + n₁ - n₂) * goldenRatio = 0 := by
    have h := h_clear
    ring_nf at h ⊢
    linarith
  -- Apply int_add_int_mul_phi_eq_zero
  -- Cast to integers properly
  have h_int := int_add_int_mul_phi_eq_zero ((n₀ : ℤ) - n₂) (2 * n₀ + n₁ - n₂)
    (by push_cast; convert h_coeff using 2)
  -- Extract: n₀ - n₂ = 0 and 2n₀ + n₁ - n₂ = 0
  have h1 : (n₀ : ℤ) = n₂ := by linarith [h_int.1]
  have h2 : (2 * (n₀ : ℤ) + n₁ : ℤ) = n₂ := by linarith [h_int.2]
  -- From h1 and h2: 2n₀ + n₁ = n₀, so n₀ + n₁ = 0
  have h3 : (n₀ : ℤ) + n₁ = 0 := by linarith
  -- Since n₀, n₁ ≥ 0, we have n₀ = n₁ = 0
  have hn0 : n₀ = 0 := by omega
  have hn1 : n₁ = 0 := by omega
  have hn2 : n₂ = 0 := by omega
  -- But n₀ + n₁ + n₂ > 0, contradiction
  omega

/-- The denominator 1 + φ + φ² is positive. -/
theorem denom_pos : 0 < 1 + goldenRatio + goldenRatio ^ 2 := by
  have h1 : 0 < goldenRatio := goldenRatio_pos
  have h2 : 0 < goldenRatio ^ 2 := sq_pos_of_pos h1
  linarith

/-- length1 = 1 / (2 * (1 + φ)) -/
theorem length1_alt : length1 = 1 / (2 * (1 + goldenRatio)) := by
  unfold length1
  rw [denom_eq_two_one_plus_phi]

/-- Interval 2 maps to [0, 0.5) under GG5 IET.
    More precisely, interval 2 = [length1 + length2, 1) maps to [0, length3).
    Since length3 = φ² * length1 and length1 + length2 = (1+φ) * length1,
    the image spans half the unit interval. -/
theorem interval2_image_bound :
    length1 + length2 = 1 / 2 := by
  have h := denom_eq_two_one_plus_phi
  unfold length1 length2
  rw [h]
  field_simp

/-- Key inequality: length3 > length1 (equivalently φ² > 1) -/
theorem length3_gt_length1 : length3 > length1 := by
  unfold length1 length3
  have hφ_gt1 : goldenRatio > 1 := Real.one_lt_goldenRatio
  have hφ_pos : goldenRatio > 0 := Real.goldenRatio_pos
  have hφ2_gt1 : goldenRatio ^ 2 > 1 := by nlinarith
  have h_denom_pos : 1 + goldenRatio + goldenRatio ^ 2 > 0 := denom_pos
  apply div_lt_div_of_pos_right _ h_denom_pos
  linarith

/-- Key inequality: length1 < 1/2 -/
theorem length1_lt_half : length1 < 1 / 2 := by
  have hφ := goldenRatio_pos
  have hφ2 : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq
  have h_denom : 1 + goldenRatio + goldenRatio ^ 2 = 2 + 2 * goldenRatio := by
    rw [hφ2]; ring
  have h_denom_pos : (0 : ℝ) < 2 + 2 * goldenRatio := by linarith
  unfold length1
  rw [h_denom]
  rw [one_div_lt_one_div h_denom_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The GG5 induced IET uses an involution permutation (swap 0 2). -/
theorem GG5_induced_IET_is_involution :
    ∀ i : Fin 3, GG5_induced_IET.permutation (GG5_induced_IET.permutation i) = i := by
  intro i
  simp only [GG5_induced_IET]
  fin_cases i <;> decide

/-- The IET function maps [0,1) to itself for involution permutations.

This is a basic property of interval exchange transformations: they permute subintervals
of [0,1), so any point in [0,1) stays in [0,1) under the transformation.

**Proof sketch:**
- For x ∈ [0,1), find interval i containing x (by intervals_cover)
- Output = rangeLeft (permutation i) + (x - domainLeft i)
- Lower bound: rangeLeft j ≥ 0 (sum of positive lengths)
- Upper bound: output < rangeRight (permutation i) ≤ 1 (sum of all lengths = 1)

**Note:** This theorem requires the permutation to be an involution (perm ∘ perm = id).
The GG5 IET uses `swap 0 2`, which satisfies this property.
-/
theorem IET_maps_to_self (iet : IntervalExchangeTransformation 3)
    (h_inv : ∀ j, iet.permutation (iet.permutation j) = j) :
    ∀ x ∈ Set.Ico 0 1, iet.toFun x ∈ Set.Ico 0 1 := by
  intro x hx
  -- Unfold the standalone toFun definition
  unfold IntervalExchangeTransformation.toFun

  -- For x ∈ [0,1), there exists i such that x ∈ interval i
  have h_cover : x ∈ ⋃ i, iet.interval i := by
    rw [iet.intervals_cover]; exact hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h_cover

  -- The epsilon chooses some value satisfying the property
  have h_exists : ∃ y, ∃ i, x ∈ iet.interval i ∧
      y = iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i) := by
    use iet.rangeLeft (iet.permutation i) + (x - iet.domainLeft i), i, hi

  -- Prove that for ANY choice satisfying the property, it's in [0,1)
  -- The property is: ∃ j, x ∈ interval j ∧ y = rangeLeft (perm j) + (x - domainLeft j)
  -- By uniqueness of intervals containing x, all such values are equal

  suffices h_suff : ∀ y, (∃ j, x ∈ iet.interval j ∧ y = iet.rangeLeft (iet.permutation j) + (x - iet.domainLeft j)) → y ∈ Ico 0 1 by
    apply h_suff
    exact Classical.epsilon_spec h_exists

  intro y ⟨j, hj_mem, hj_eq⟩
  rw [hj_eq]

  -- Now prove rangeLeft (perm j) + (x - domainLeft j) ∈ [0,1)
  constructor
  · -- Lower bound: 0 ≤ output
    have h_range_nn : 0 ≤ iet.rangeLeft (iet.permutation j) := by
      unfold IntervalExchangeTransformation.rangeLeft
      apply Finset.sum_nonneg
      intro k _
      exact le_of_lt (iet.lengths_pos _)
    have h_offset_nn : 0 ≤ x - iet.domainLeft j := by
      have : x ∈ iet.interval j := hj_mem
      unfold IntervalExchangeTransformation.interval at this
      linarith [this.1]
    linarith
  · -- Upper bound: output < 1
    -- x - domainLeft j < lengths j
    have h_offset_lt : x - iet.domainLeft j < iet.lengths j := by
      have : x ∈ iet.interval j := hj_mem
      unfold IntervalExchangeTransformation.interval IntervalExchangeTransformation.domainRight at this
      linarith [this.2]
    -- rangeRight (perm j) ≤ 1
    have h_rangeRight_le : iet.rangeRight (iet.permutation j) ≤ 1 := by
      unfold IntervalExchangeTransformation.rangeRight IntervalExchangeTransformation.rangeLeft
      -- Sum of first (perm j).val lengths + length (perm j) ≤ sum of all lengths = 1
      let k := iet.permutation j
      have h_le : k.val.succ ≤ 3 := k.isLt
      calc ∑ m : Fin k.val, iet.lengths (iet.permutation ⟨m, Nat.lt_trans m.isLt k.isLt⟩) + iet.lengths (iet.permutation k)
          = ∑ m : Fin k.val.succ, iet.lengths (iet.permutation ⟨m, Nat.lt_of_lt_of_le m.isLt h_le⟩) := by
            rw [Fin.sum_univ_castSucc]; congr 1
        _ ≤ ∑ m : Fin 3, iet.lengths (iet.permutation m) := by
            have h_image : Finset.univ.image (Fin.castLE h_le) ⊆ Finset.univ := by simp
            calc ∑ m : Fin k.val.succ, iet.lengths (iet.permutation ⟨m, Nat.lt_of_lt_of_le m.isLt h_le⟩)
                = ∑ m : Fin k.val.succ, iet.lengths (iet.permutation (Fin.castLE h_le m)) := by rfl
              _ = ∑ m ∈ Finset.univ.image (Fin.castLE h_le), iet.lengths (iet.permutation m) := by
                  rw [Finset.sum_image]; intro _ _ _ _ h; exact Fin.castLE_injective h_le h
              _ ≤ ∑ m : Fin 3, iet.lengths (iet.permutation m) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg h_image
                  intro m _ _; exact le_of_lt (iet.lengths_pos _)
        _ = ∑ m : Fin 3, iet.lengths m := by
            have : ∑ m : Fin 3, iet.lengths (iet.permutation m) = ∑ m : Fin 3, iet.lengths m :=
              Equiv.sum_comp iet.permutation iet.lengths
            exact this
        _ = 1 := iet.lengths_sum
    have h_sum_le : iet.rangeLeft (iet.permutation j) + iet.lengths j ≤ 1 := by
      -- Strategy: Use h_rangeRight_le which gives us:
      -- rangeLeft (perm j) + lengths (perm (perm j)) ≤ 1
      -- If we can show lengths j ≤ lengths (perm (perm j)), we're done.

      unfold IntervalExchangeTransformation.rangeRight at h_rangeRight_le
      -- h_rangeRight_le : rangeLeft (perm j) + lengths (perm (perm j)) ≤ 1

      -- Use the involution hypothesis: perm (perm j) = j
      calc iet.rangeLeft (iet.permutation j) + iet.lengths j
          = iet.rangeLeft (iet.permutation j) + iet.lengths (iet.permutation (iet.permutation j)) := by rw [h_inv j]
        _ ≤ 1 := h_rangeRight_le

    linarith [h_sum_le, h_offset_lt]

/-- length1/2 is in the unit interval [0,1). -/
theorem length1_half_mem_Ico : length1 / 2 ∈ Set.Ico 0 1 := by
  constructor
  · apply le_of_lt
    apply div_pos; exact length1_pos; norm_num
  · calc length1 / 2 = length1 * (1 / 2) := by ring
      _ < length1 * 1 := by
        apply mul_lt_mul_of_pos_left
        · norm_num
        · exact length1_pos
      _ = length1 := by ring
      _ < 1 := by
        have : length1 + length2 + length3 = 1 := lengths_sum_to_one
        linarith [length2_pos, length3_pos]

/-- All iterates of length1/2 under the GG5 IET remain in [0,1). -/
theorem GG5_IET_iterate_mem_Ico (n : ℕ) :
    (GG5_induced_IET.toFun^[n]) (length1 / 2) ∈ Set.Ico 0 1 := by
  induction n with
  | zero => simp; exact length1_half_mem_Ico
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    apply IET_maps_to_self _ GG5_induced_IET_is_involution
    exact ih

/-- The iterates of length1/2 under the GG5 IET are all distinct.

This is proven by showing that if f^[n](x) = f^[m](x) for some n ≠ m,
then a linear combination of 1 and φ equals zero with non-trivial integer
coefficients, contradicting the irrationality of φ.

The key insight is that the cumulative displacement after k steps is of
the form (a + b·φ)/(1+φ+φ²) for some integers a, b depending on which
intervals are visited. By the linear independence of {1, φ} over ℤ
(proven in `int_add_int_mul_phi_eq_zero`), distinct visit patterns give
distinct positions.
-/
theorem GG5_IET_iterates_injective :
    Function.Injective (fun n : ℕ => (GG5_induced_IET.toFun^[n]) (length1 / 2)) := by
  -- Prove by contrapositive: if f^[m] x = f^[n] x with m ≠ n,
  -- then some orbit point is periodic, contradicting the infinite orbit property
  intro m n hmn
  by_contra h_ne
  -- WLOG assume m < n
  wlog h_lt : m < n generalizing m n with H
  · have h_gt : n < m := Nat.lt_of_le_of_ne (Nat.not_lt.mp h_lt) (Ne.symm h_ne)
    exact H hmn.symm (Ne.symm h_ne) h_gt
  -- f^[m] x = f^[n] x with m < n means f^[m] x is periodic
  have h_periodic : (GG5_induced_IET.toFun^[m]) (length1 / 2) ∈ Function.periodicPts GG5_induced_IET.toFun := by
    have h_period : 0 < n - m := Nat.sub_pos_of_lt h_lt
    have h_eq : (GG5_induced_IET.toFun^[n - m]) ((GG5_induced_IET.toFun^[m]) (length1 / 2)) =
                (GG5_induced_IET.toFun^[m]) (length1 / 2) := by
      calc (GG5_induced_IET.toFun^[n - m]) ((GG5_induced_IET.toFun^[m]) (length1 / 2))
          = (GG5_induced_IET.toFun^[n - m + m]) (length1 / 2) := by rw [Function.iterate_add_apply]
        _ = (GG5_induced_IET.toFun^[n]) (length1 / 2) := by congr 1; omega
        _ = (GG5_induced_IET.toFun^[m]) (length1 / 2) := hmn.symm
    exact Function.mk_mem_periodicPts h_period h_eq
  -- The periodic point is in [0,1)
  have h_mem : (GG5_induced_IET.toFun^[m]) (length1 / 2) ∈ Set.Ico 0 1 :=
    GG5_IET_iterate_mem_Ico m
  -- Get the minimal period
  let p := Function.minimalPeriod GG5_induced_IET.toFun ((GG5_induced_IET.toFun^[m]) (length1 / 2))
  have hp_pos : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts h_periodic
  -- The point y = f^[m](x) has minimal period p
  -- After p applications of f, we return to y
  have h_return : (GG5_induced_IET.toFun^[p]) ((GG5_induced_IET.toFun^[m]) (length1 / 2)) =
                  (GG5_induced_IET.toFun^[m]) (length1 / 2) :=
    Function.isPeriodicPt_minimalPeriod _ _
  -- Now we derive contradiction using the algebraic structure
  -- The displacement from y back to y after p steps must be 0
  -- But the golden ratio structure prevents this for any p > 0

  -- Key facts about the IET:
  have h_half : length1 + length2 = 1 / 2 := interval2_image_bound
  have h_length3_half : length3 = 1 / 2 := by
    have h := lengths_sum_to_one; linarith

  -- The displacement when visiting interval i is:
  -- d₀ = rangeLeft(2) - domainLeft(0) = (length3 + length2) - 0 = 1 - length1
  -- d₁ = rangeLeft(1) - domainLeft(1) = length3 - length1 = 1/2 - length1 = length2
  -- d₂ = rangeLeft(0) - domainLeft(2) = 0 - (length1 + length2) = -1/2

  -- For return: n₀·d₀ + n₁·d₁ + n₂·d₂ = 0 where n_i counts visits
  -- n₀(1 - length1) + n₁·length2 + n₂(-1/2) = 0
  -- n₀ - n₀·length1 + n₁·length2 - n₂/2 = 0

  -- Now length1 = 1/(1+φ+φ²), length2 = φ/(1+φ+φ²)
  -- And 1+φ+φ² = 2(1+φ) by denom_eq_two_one_plus_phi

  -- So: n₀ - n₀/(2(1+φ)) + n₁φ/(2(1+φ)) - n₂/2 = 0
  -- Multiply by 2(1+φ):
  -- 2n₀(1+φ) - n₀ + n₁φ - n₂(1+φ) = 0
  -- 2n₀ + 2n₀φ - n₀ + n₁φ - n₂ - n₂φ = 0
  -- (2n₀ - n₀ - n₂) + (2n₀ + n₁ - n₂)φ = 0
  -- (n₀ - n₂) + (2n₀ + n₁ - n₂)φ = 0

  -- By int_add_int_mul_phi_eq_zero, this means:
  -- n₀ - n₂ = 0 AND 2n₀ + n₁ - n₂ = 0
  -- So n₀ = n₂ AND 2n₀ + n₁ = n₂ = n₀
  -- Therefore n₀ + n₁ = 0

  -- Since n_i ≥ 0 and n₀ + n₁ + n₂ = p > 0, we need n₂ > 0
  -- But n₀ = n₂ and n₀ + n₁ = 0 means n₀ = n₁ = 0
  -- So n₂ = n₀ = 0, contradicting p > 0

  -- This algebraic argument is the core - it shows no periodic orbit can exist
  -- We would need to formalize the visit counting and displacement calculation

  -- For now, we use a more direct approach: show that distinct iterates give distinct values
  -- by tracking the cumulative displacement modulo the φ-structure

  -- Alternative direct argument:
  -- The return condition f^[p](y) = y means the cumulative displacement is 0
  -- But the cumulative displacement has the form (a + b·φ)/(2(1+φ)) for integers a, b
  -- For this to be 0, we need a + b·φ = 0, so a = b = 0 by int_add_int_mul_phi_eq_zero
  -- But a and b depend on the visit counts, and a = b = 0 forces all visit counts to be 0
  -- This contradicts p > 0

  -- The formal proof requires computing the displacement function explicitly
  -- For brevity, we use the contrapositive of the orbit infrastructure

  -- Since we've shown orbit points are in [0,1), and periodicity would violate
  -- the golden ratio structure, we conclude m = n

  -- Actually, the cleanest approach is to note that if the iterate map were not injective,
  -- the orbit would be finite, but finite orbits imply periodicity (by Orbit.finite_orbit_implies_periodic)
  -- and periodicity creates the displacement equation that has only the trivial solution

  exfalso
  -- We have a periodic point y = f^[m](x) in [0,1) with period p > 0
  -- The return condition f^[p](y) = y means cumulative displacement over p steps = 0

  -- Set y = f^[m](x)
  let y := (GG5_induced_IET.toFun^[m]) (length1 / 2)

  -- All iterates of y also stay in [0,1)
  have h_iter_mem : ∀ k < p, (GG5_induced_IET.toFun^[k]) y ∈ Set.Ico 0 1 := by
    intro k _
    -- y = f^[m](x), so f^[k](y) = f^[k+m](x)
    have h_eq : (GG5_induced_IET.toFun^[k]) y = (GG5_induced_IET.toFun^[k + m]) (length1 / 2) := by
      calc (GG5_induced_IET.toFun^[k]) y
          = (GG5_induced_IET.toFun^[k]) ((GG5_induced_IET.toFun^[m]) (length1 / 2)) := rfl
        _ = (GG5_induced_IET.toFun^[k + m]) (length1 / 2) := by rw [Function.iterate_add_apply]
    rw [h_eq]
    exact GG5_IET_iterate_mem_Ico (k + m)

  -- Cumulative displacement over p steps equals f^[p](y) - y = 0
  have h_cum_zero : cumulative_displacement y p = 0 := by
    rw [cumulative_displacement_telescope y p h_iter_mem, h_return, sub_self]

  -- Now we need to show that cumulative_displacement y p can be written as
  -- n₀*d₀ + n₁*d₁ + n₂*d₂ for some natural numbers n₀, n₁, n₂ with n₀ + n₁ + n₂ = p

  -- Define visit counts: count how many times each interval is visited
  let visits_0 := Finset.filter (fun k => (GG5_induced_IET.toFun^[k]) y < length1) (Finset.range p)
  let visits_1 := Finset.filter (fun k => length1 ≤ (GG5_induced_IET.toFun^[k]) y ∧
                                          (GG5_induced_IET.toFun^[k]) y < length1 + length2) (Finset.range p)
  let visits_2 := Finset.filter (fun k => length1 + length2 ≤ (GG5_induced_IET.toFun^[k]) y) (Finset.range p)

  -- The cumulative displacement equals the sum of displacements at each step
  have h_cum_expand : cumulative_displacement y p =
      ∑ k ∈ Finset.range p, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) := rfl

  -- Each step contributes one of d₀, d₁, or d₂ based on which interval is visited
  have h_disp_cases : ∀ k ∈ Finset.range p,
      GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
        if (GG5_induced_IET.toFun^[k]) y < length1 then displacement0
        else if (GG5_induced_IET.toFun^[k]) y < length1 + length2 then displacement1
        else displacement2 := by
    intro k _
    rfl

  -- Split the sum by interval membership
  -- cumulative_displacement y p = visits_0.card * d₀ + visits_1.card * d₁ + visits_2.card * d₂
  have h_partition : Finset.range p = visits_0 ∪ visits_1 ∪ visits_2 := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, visits_0, visits_1, visits_2]
    constructor
    · intro hk
      by_cases h0 : (GG5_induced_IET.toFun^[k]) y < length1
      · left; left; exact ⟨hk, h0⟩
      · by_cases h1 : (GG5_induced_IET.toFun^[k]) y < length1 + length2
        · left; right
          push_neg at h0
          exact ⟨hk, h0, h1⟩
        · right
          push_neg at h1
          exact ⟨hk, h1⟩
    · intro h
      rcases h with ((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk

  have h_disjoint_01 : Disjoint visits_0 visits_1 := by
    simp only [Finset.disjoint_iff_ne, visits_0, visits_1, Finset.mem_filter]
    intro a ⟨_, ha0⟩ b ⟨_, hb1, _⟩ hab
    rw [hab] at ha0
    linarith

  have h_disjoint_02 : Disjoint visits_0 visits_2 := by
    simp only [Finset.disjoint_iff_ne, visits_0, visits_2, Finset.mem_filter]
    intro a ⟨_, ha0⟩ b ⟨_, hb2⟩ hab
    subst hab
    -- Now ha0 says f^[a] y < length1, but hb2 says length1 + length2 ≤ f^[a] y
    linarith [length2_pos]

  have h_disjoint_12 : Disjoint visits_1 visits_2 := by
    simp only [Finset.disjoint_iff_ne, visits_1, visits_2, Finset.mem_filter]
    intro a ⟨_, _, ha1⟩ b ⟨_, hb2⟩ hab
    rw [hab] at ha1
    linarith

  -- The sum splits into three parts
  have h_sum_split : ∑ k ∈ Finset.range p, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
      ∑ k ∈ visits_0, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) +
      ∑ k ∈ visits_1, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) +
      ∑ k ∈ visits_2, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) := by
    rw [h_partition]
    -- Union is left-associative: (visits_0 ∪ visits_1) ∪ visits_2
    have h_disjoint_01_2 : Disjoint (visits_0 ∪ visits_1) visits_2 :=
      Finset.disjoint_union_left.mpr ⟨h_disjoint_02, h_disjoint_12⟩
    rw [Finset.sum_union h_disjoint_01_2, Finset.sum_union h_disjoint_01]

  -- In visits_0, displacement = d₀
  have h_sum_0 : ∑ k ∈ visits_0, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
                 visits_0.card * displacement0 := by
    have h_all_eq : ∀ k ∈ visits_0, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) = displacement0 := by
      intro k hk
      simp only [Finset.mem_filter, visits_0] at hk
      unfold GG5_displacement
      simp [hk.2]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  -- In visits_1, displacement = d₁
  have h_sum_1 : ∑ k ∈ visits_1, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
                 visits_1.card * displacement1 := by
    have h_all_eq : ∀ k ∈ visits_1, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) = displacement1 := by
      intro k hk
      simp only [Finset.mem_filter, visits_1] at hk
      unfold GG5_displacement
      have h_not_0 : ¬ (GG5_induced_IET.toFun^[k]) y < length1 := by linarith [hk.2.1]
      simp [h_not_0, hk.2.2]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  -- In visits_2, displacement = d₂
  have h_sum_2 : ∑ k ∈ visits_2, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) =
                 visits_2.card * displacement2 := by
    have h_all_eq : ∀ k ∈ visits_2, GG5_displacement ((GG5_induced_IET.toFun^[k]) y) = displacement2 := by
      intro k hk
      simp only [Finset.mem_filter, visits_2] at hk
      unfold GG5_displacement
      have h_not_0 : ¬ (GG5_induced_IET.toFun^[k]) y < length1 := by
        linarith [hk.2, length2_pos]
      have h_not_1 : ¬ (GG5_induced_IET.toFun^[k]) y < length1 + length2 := by linarith [hk.2]
      simp [h_not_0, h_not_1]
    rw [Finset.sum_eq_card_nsmul h_all_eq, nsmul_eq_mul]

  -- Combine: cumulative_displacement = n₀*d₀ + n₁*d₁ + n₂*d₂
  have h_cum_as_sum : cumulative_displacement y p =
      visits_0.card * displacement0 + visits_1.card * displacement1 + visits_2.card * displacement2 := by
    rw [h_cum_expand, h_sum_split, h_sum_0, h_sum_1, h_sum_2]

  -- The visit counts sum to p
  have h_card_sum : visits_0.card + visits_1.card + visits_2.card = p := by
    have h_disj1 : Disjoint visits_0 (visits_1 ∪ visits_2) :=
      Finset.disjoint_union_right.mpr ⟨h_disjoint_01, h_disjoint_02⟩
    have h_disj2 : Disjoint visits_1 visits_2 := h_disjoint_12
    calc visits_0.card + visits_1.card + visits_2.card
        = visits_0.card + (visits_1.card + visits_2.card) := by ring
      _ = visits_0.card + (visits_1 ∪ visits_2).card := by
          rw [Finset.card_union_of_disjoint h_disj2]
      _ = (visits_0 ∪ (visits_1 ∪ visits_2)).card := by
          rw [Finset.card_union_of_disjoint h_disj1]
      _ = (visits_0 ∪ visits_1 ∪ visits_2).card := by
          rw [Finset.union_assoc]
      _ = (Finset.range p).card := by rw [← h_partition]
      _ = p := Finset.card_range p

  -- Since p > 0, we have visits_0.card + visits_1.card + visits_2.card > 0
  have h_sum_pos : 0 < visits_0.card + visits_1.card + visits_2.card := by
    rw [h_card_sum]; exact hp_pos

  -- But displacement_sum_ne_zero says the weighted sum ≠ 0
  have h_ne_zero := displacement_sum_ne_zero visits_0.card visits_1.card visits_2.card h_sum_pos

  -- This contradicts h_cum_zero
  rw [h_cum_as_sum] at h_cum_zero
  exact h_ne_zero h_cum_zero

/-- **Main Theorem**: The GG5-induced interval exchange transformation
has points with infinite orbits.

**Proof Strategy (Direct Injectivity):**
We show that for x = length1/2, all iterates f^[n](x) are distinct.
Since ℕ is infinite and the iterate map is injective, the orbit set is infinite.

This avoids the need to prove universal non-periodicity (Keane's theorem).
Instead, we use the algebraic structure of the golden ratio directly.
-/
theorem GG5_IET_has_infinite_orbit :
    ∃ (x : ℝ), x ∈ Set.Ico 0 1 ∧
      (Orbit.orbitSet GG5_induced_IET.toFun x).Infinite := by
  use length1 / 2
  constructor
  · exact length1_half_mem_Ico
  · -- The orbit is infinite because the iterate map is injective
    apply Set.infinite_of_injective_forall_mem GG5_IET_iterates_injective
    intro n
    exact Orbit.orbitSet_iterate _ _ n

end TDCSG.CompoundSymmetry.GG5
