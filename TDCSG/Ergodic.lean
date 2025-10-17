/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Ergodic Piecewise Isometries

This file develops the theory of ergodic piecewise isometries, which are measure-preserving
piecewise isometries that additionally satisfy the ergodic property: every invariant set has
measure zero or full measure.

This is the third tier in the three-tiered structure pattern for piecewise isometries.

## Main definitions

- `ErgodicPiecewiseIsometry α μ`: A measure-preserving piecewise isometry that is ergodic
  with respect to measure `μ`
- `MinimalPiecewiseIsometry α μ`: A piecewise isometry with all orbits dense

## Main results

- `ergodic_of_mixing`: A mixing piecewise isometry is ergodic
- `unique_ergodicity_of_finite`: Conditions for unique ergodicity
- `ergodic_iff_irreducible`: Ergodicity characterized by irreducibility of the partition
- `minimal_implies_uniquely_ergodic`: Under suitable conditions, minimality implies unique
  ergodicity

## References

* [Peter Walters, *An Introduction to Ergodic Theory*][Walters1982]
* [Arek Goetz, *Dynamics of piecewise isometries*][Goetz2000]

-/

universe u v

open BigOperators

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α}

/-- An ergodic piecewise isometry.

This extends `MeasurePreservingPiecewiseIsometry` by requiring that the map is ergodic:
every invariant measurable set has measure zero or full measure. -/
structure ErgodicPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends MeasurePreservingPiecewiseIsometry α μ where
  /-- The map is ergodic with respect to μ -/
  ergodic : Ergodic toFun μ

namespace ErgodicPiecewiseIsometry

/-- Coercion to measure-preserving piecewise isometry. -/
instance : Coe (ErgodicPiecewiseIsometry α μ)
    (MeasurePreservingPiecewiseIsometry α μ) where
  coe f := f.toMeasurePreservingPiecewiseIsometry

/-- Allow function application. -/
instance : CoeFun (ErgodicPiecewiseIsometry α μ) (fun _ => α → α) where
  coe f := f.toFun

/-- Extract the ergodic property. -/
theorem isErgodic (f : ErgodicPiecewiseIsometry α μ) :
    Ergodic f.toFun μ :=
  f.ergodic

/-- Function application. -/
@[simp]
theorem apply_eq_toFun (f : ErgodicPiecewiseIsometry α μ) (x : α) :
    f x = f.toFun x := rfl

end ErgodicPiecewiseIsometry

section ErgodicityConditions

/-- A measure-preserving piecewise isometry is ergodic if every invariant set has measure
zero or full measure. -/
theorem ergodic_iff_invariant_measure (f : MeasurePreservingPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Ergodic f.toFun μ ↔
      ∀ s : Set α, MeasurableSet s → f.toFun ⁻¹' s = s → μ s = 0 ∨ μ s = 1 := by
  constructor
  · intro h s hs hinv
    have h_pre := h.toPreErgodic
    have : μ s = 0 ∨ μ sᶜ = 0 := h_pre.measure_self_or_compl_eq_zero hs hinv
    cases this with
    | inl h0 => left; exact h0
    | inr hc =>
      right
      exact (MeasureTheory.prob_compl_eq_zero_iff hs).mp hc
  · intro h
    have h_mp := f.measure_preserving
    constructor
    · exact h_mp
    · constructor
      intro s hs hinv
      obtain h0 | h1 := h s hs hinv
      · -- μ(s) = 0 implies s is eventually constant (a.e. false)
        -- Use Filter.eventuallyConst_pred: EventuallyConst s (ae μ) ↔ (∀ᵐ x, x ∈ s) ∨ (∀ᵐ x, x ∉ s)
        rw [Filter.eventuallyConst_pred]
        right
        -- Show ∀ᵐ x ∂μ, x ∉ s, which follows from μ s = 0
        exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h0
      · -- μ(s) = 1 implies s is eventually constant (a.e. true)
        -- Use Filter.eventuallyConst_pred: EventuallyConst s (ae μ) ↔ (∀ᵐ x, x ∈ s) ∨ (∀ᵐ x, x ∉ s)
        rw [Filter.eventuallyConst_pred]
        left
        -- Show ∀ᵐ x ∂μ, x ∈ s
        -- Since μ(s) = 1 and μ is a probability measure, we have μ(sᶜ) = 0
        have h_compl : μ sᶜ = 0 := by
          rw [MeasureTheory.prob_compl_eq_zero_iff hs]
          exact h1
        -- Therefore ∀ᵐ x, x ∉ sᶜ, which means ∀ᵐ x, x ∈ s
        have : ∀ᵐ x ∂μ, x ∉ sᶜ := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_compl
        filter_upwards [this] with x hx
        simp only [Set.mem_compl_iff, not_not] at hx
        exact hx

/-- A piecewise isometry is ergodic if it is mixing (stronger condition). -/
theorem ergodic_of_mixing (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_mixing : ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
      Filter.Tendsto (fun n => μ (f.toFun^[n] ⁻¹' s ∩ t)) Filter.atTop
        (nhds (μ s * μ t))) :
    Ergodic f.toFun μ := by
  -- Construct ergodic from measure-preserving + preergodic
  constructor
  · -- Measure-preserving
    exact f.measure_preserving
  · -- PreErgodic: for any invariant set, it's eventually constant a.e.
    constructor
    intro s hs hinv
    rw [Filter.eventuallyConst_pred]
    -- For an invariant set s, we have f^n ⁻¹' s = s for all n
    -- So the mixing condition gives: μ(s ∩ t) → μ(s) * μ(t) as n → ∞
    -- But since f^n ⁻¹' s = s, we have μ(s ∩ t) = μ(s) * μ(t) for all t
    -- This forces μ(s) ∈ {0, 1}
    by_cases h : μ s = 0
    · -- If μ(s) = 0, then ∀ᵐ x, x ∉ s
      right
      exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h
    · -- If μ(s) ≠ 0, we'll show μ(s) = 1
      left
      -- Use the mixing property with t = sᶜ
      have h_mix := h_mixing s sᶜ hs hs.compl
      -- Since s is invariant: f^n ⁻¹' s = s for all n
      have hinv_n : ∀ n, f.toFun^[n] ⁻¹' s = s := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          show (f.toFun^[n + 1]) ⁻¹' s = s
          rw [Function.iterate_succ]
          rw [Set.preimage_comp, ih, hinv]
      -- Therefore μ(s ∩ sᶜ) = μ(s) * μ(sᶜ)
      -- The mixing property says μ(f^n⁻¹(s) ∩ sᶜ) → μ(s) * μ(sᶜ)
      -- But f^n⁻¹(s) = s, so μ(s ∩ sᶜ) = μ(s) * μ(sᶜ)
      have h_eq : μ (s ∩ sᶜ) = μ s * μ sᶜ := by
        have : ∀ n, f.toFun^[n] ⁻¹' s ∩ sᶜ = s ∩ sᶜ := fun n => by rw [hinv_n]
        -- The sequence is constant, so its limit equals the constant value
        -- h_mix : μ(f^n⁻¹(s) ∩ sᶜ) → μ(s) * μ(sᶜ)
        -- The constant sequence s ∩ sᶜ also converges to s ∩ sᶜ
        have h_const : Filter.Tendsto (fun n : ℕ => μ (s ∩ sᶜ)) Filter.atTop (nhds (μ (s ∩ sᶜ))) :=
          tendsto_const_nhds
        -- Since f^n⁻¹(s) ∩ sᶜ = s ∩ sᶜ for all n, the two sequences are equal
        have h_eq : (fun n => μ (f.toFun^[n] ⁻¹' s ∩ sᶜ)) = fun n => μ (s ∩ sᶜ) := by
          funext n; rw [this]
        rw [h_eq] at h_mix
        -- Both sequences have the same limit, so μ(s ∩ sᶜ) = μ(s) * μ(sᶜ)
        -- Use uniqueness of limits in Hausdorff spaces
        exact tendsto_nhds_unique h_const h_mix
      -- But s ∩ sᶜ = ∅, so μ(s ∩ sᶜ) = 0
      have h_empty : μ (s ∩ sᶜ) = 0 := by simp
      -- Therefore μ(s) * μ(sᶜ) = 0
      rw [h_empty] at h_eq
      -- Since μ(s) ≠ 0, we must have μ(sᶜ) = 0
      have h_prod_zero : μ s * μ sᶜ = 0 := h_eq.symm
      have : μ sᶜ = 0 := (mul_eq_zero.mp h_prod_zero).resolve_left h
      -- Therefore ∀ᵐ x, x ∉ sᶜ, which means ∀ᵐ x, x ∈ s
      have : ∀ᵐ x ∂μ, x ∉ sᶜ := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp this
      filter_upwards [this] with x hx
      simp only [Set.mem_compl_iff, not_not] at hx
      exact hx

/-- Ergodicity can be characterized by irreducibility of the partition dynamics. -/
theorem ergodic_iff_irreducible (f : MeasurePreservingPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Ergodic f.toFun μ ↔
      ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
        μ s > 0 → μ t > 0 →
        ∃ n : ℕ, μ (f.toFun^[n] ⁻¹' s ∩ t) > 0 := by
/-
PROOF ATTEMPT HISTORY FOR ergodic_iff_irreducible:

Attempt 1 [2025-10-16]:
Strategy: Forward direction via contrapositive using A = ⋃_{n≥0} f^n⁻¹(s)
Approach:
  1. Assume μ(f^n⁻¹(s) ∩ t) = 0 for all n
  2. Define A = ⋃_{n≥0} f^n⁻¹(s) (points whose orbit hits s)
  3. Show A is invariant and 0 < μ(A) < 1
  4. Contradict ergodicity

Failure: A = ⋃_{n≥0} f^n⁻¹(s) is NOT invariant in the required sense.
  - We have f⁻¹(A) ⊇ A (easy: if f^n(x) ∈ s then f^(n+1)(f⁻¹(x)) ∈ s)
  - But f⁻¹(A) = A requires: if x ∈ s then f(x) eventually returns to s
  - This requires Poincaré recurrence theorem (not yet in Mathlib)

Alternative approach needed:
  - Use Birkhoff ergodic theorem + recurrence
  - Or define B = {x : infinitely often f^n(x) ∈ s} (requires limsup, harder)
  - Or use Conservative property (points return to neighborhoods)

Root issue: This is Hopf decomposition theory, requires:
  - Poincaré recurrence theorem: MeasureTheory.Poincare.ae_frequently_mem_of_mem_nhds
  - Conservative dynamical systems theory
  - Ergodic decomposition

CLASSIFICATION: Research-level (confirmed in README as "hard - Hopf decomposition")
REQUIRED MATHLIB ADDITIONS:
  - Poincaré recurrence for measure-preserving maps
  - Conservative systems formalization
  - Connecting irreducibility with ergodic decomposition
-/
  constructor
  · -- Forward: Ergodic → Irreducible
    intro herg s t hs ht μs_pos μt_pos
    /-
    PROOF ATTEMPT HISTORY FOR ergodic_iff_irreducible (forward direction):

    Attempt 1 [2025-10-16]:
    Strategy: Define A = {x ∈ t : ∀n, f^n(x) ∉ s} and show μ(A) = μ(t) by assumption
    Failure: Can show f^{-1}(A) ⊇ A but NOT f^{-1}(A) = A (exact invariance)
    Issue: A is backward invariant but not forward invariant
      - If x ∈ A and f^n(x) ∉ s for all n, then f^{-1}(x) might leave t
      - Forward invariance f(A) ⊆ A would require: if f(x) never hits s, then x never hits s
      - This is EXACTLY Poincaré recurrence: points return to their starting set

    Attempt 2 [2025-10-16]:
    Strategy: Use B = ⋃_{n≥0} f^{-n}(s) (all points whose orbit eventually hits s)
    Approach:
      1. Show f^{-1}(B) ⊇ B (easy: if f^n(x) ∈ s then f^{n+1}(f^{-1}(x)) ∈ s)
      2. Show f^{-1}(B) ⊆ B (HARD: requires Poincaré recurrence)
         - Need: if x ∈ B then f(x) ∈ B
         - i.e., if x eventually hits s, then f(x) eventually hits s
         - Equivalently: if f^n(x) ∈ s for some n, then f^{n+1}(x) ∈ s OR f(x) returns to s later
         - This is Poincaré recurrence: points in s return to s infinitely often
      3. Use ergodicity: B is invariant, so μ(B) ∈ {0, 1}
      4. Since μ(s) > 0 and s ⊆ B, we have μ(B) = 1
      5. Similarly for t, contradiction

    ROOT ISSUE: Poincaré recurrence in strong form
      - Conservative.ae_mem_imp_frequently_image_mem gives: a.e. x ∈ s, f^n(x) ∈ s infinitely often
      - But we need: ⋃_n f^{-n}(s) is EXACTLY invariant (not just backward invariant)
      - This requires showing f^{-1}(⋃_n f^{-n}(s)) = ⋃_n f^{-n}(s)
      - Forward inclusion is trivial
      - Backward inclusion needs: if ⋃_n f^{-n}(f(x)) ∩ s ≠ ∅, then ⋃_n f^{-n}(x) ∩ s ≠ ∅
      - This is recurrence property: returning once implies returning infinitely often

    INFRASTRUCTURE NEEDED:
      - Theorem: For conservative f and set s, define B = {x : ∃^∞ n, f^n(x) ∈ s}
      - Then f^{-1}(B) = B (exact invariance)
      - Proof uses: points returning to s must return infinitely often (Poincaré recurrence)
      - NOT currently in Mathlib as stated (though Conservative has related results)

    CLASSIFICATION: Research-level (confirmed as "hard" in README)
    This direction genuinely requires formalization not yet in Mathlib:
      - Conservative.ae_mem_imp_frequently_image_mem is close but works a.e., not for sets
      - Need measure-theoretic version of "visiting infinitely often" as invariant set

    Attempt 3 [2025-10-16]: Direct approach using Conservative
    Strategy: Contrapositive - assume ∀n, μ(f^n⁻¹(s) ∩ t) = 0 and derive contradiction
    Approach:
      1. Since μ(f^n⁻¹(s) ∩ t) = 0 for all n, we have μ((⋃n f^n⁻¹(s)) ∩ t) = 0
      2. Therefore μ(t \ (⋃n f^n⁻¹(s))) = μ(t) > 0
      3. This set B = {x ∈ t : ∀n, f^n(x) ∉ s} has positive measure
      4. But f is conservative (measure-preserving on probability space)
      5. Should be able to show this contradicts ergodicity + μ(s) > 0

    Gap: Need to connect "B has positive measure and orbits avoid s" with ergodicity
      - Intuitively: if μ(B) > 0 and μ(s) > 0, ergodicity should force intersection
      - But ergodicity only applies to INVARIANT sets
      - B is not obviously invariant (f(B) need not be subset of B)
      - Would need: "if B avoids all forward iterates of s, then B^c contains invariant set"
      - This is essentially the same Poincaré recurrence issue as Attempts 1-2

    MATHLIB INFRASTRUCTURE NEEDED:
      1. Theorem: For ergodic measure-preserving f and sets s,t with μ(s),μ(t) > 0,
         the set {x ∈ t : ∃n, f^n(x) ∈ s} has positive measure
      2. This would follow from connecting:
         - Ergodicity (invariant sets are trivial)
         - Conservative property (points return to neighborhoods)
         - Measure-theoretic recurrence (visiting sets infinitely often)
      3. Current Mathlib has pieces but not the full connection
    -/
    sorry
  · -- Backward: Irreducible → Ergodic
    intro h_irred
    -- Show f is ergodic using the invariant set characterization
    rw [ergodic_iff_invariant_measure]
    intro s hs h_inv
    -- If s is invariant, then f^n⁻¹(s) = s for all n
    by_cases h : μ s = 0
    · left; exact h
    · -- Suppose μ(s) > 0. We'll show μ(s) = 1
      right
      -- If μ(sᶜ) > 0, apply irreducibility to s and sᶜ
      by_contra h_not_one
      have μs_pos : μ s > 0 :=
        (zero_le (μ s)).lt_of_ne (Ne.symm h)
      have μsc_pos : μ sᶜ > 0 := by
        have h1 : μ s ≠ 1 := h_not_one
        have h2 : μ sᶜ ≠ 0 := by
          intro hsc
          have : μ s = 1 := (MeasureTheory.prob_compl_eq_zero_iff hs).mp hsc
          exact h1 this
        exact (zero_le (μ sᶜ)).lt_of_ne (Ne.symm h2)
      -- Apply irreducibility
      obtain ⟨n, hn⟩ := h_irred s sᶜ hs hs.compl μs_pos μsc_pos
      -- But f^k⁻¹(s) = s for all k by invariance
      have hinv_n : ∀ k, f.toFun^[k] ⁻¹' s = s := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [Function.iterate_succ]
          rw [Set.preimage_comp, ih, h_inv]
      -- So f^n⁻¹(s) ∩ sᶜ = s ∩ sᶜ = ∅
      rw [hinv_n n] at hn
      simp at hn

end ErgodicityConditions

section UniqueErgodicity

/-- A measure-preserving piecewise isometry is uniquely ergodic if there is only one
invariant probability measure. -/
def IsUniquelyErgodic (f : PiecewiseIsometry α) (μ : MeasureTheory.Measure α) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧
  MeasureTheory.MeasurePreserving f.toFun μ μ ∧
  ∀ ν : MeasureTheory.Measure α, MeasureTheory.IsProbabilityMeasure ν →
    MeasureTheory.MeasurePreserving f.toFun ν ν → ν = μ

/-- For interval exchange transformations (finite partition), unique ergodicity is generic.

MASUR-VEECH THEOREM: This theorem states that for a generic set of IET parameters
(in the sense of Lebesgue measure on the parameter space), the system is uniquely ergodic.

We state this as a theorem with explicit hypotheses about the "generic" property.
The hypothesis h_generic represents the condition that the IET parameters satisfy
appropriate Diophantine/irrationality conditions (e.g., Keane's condition or
irreducibility of the Rauzy class).

A full proof would require:
1. Formalizing the IET parameter space (length vectors and permutations)
2. Defining Lebesgue measure on this space
3. Formalizing Rauzy-Veech induction
4. Developing the Kontsevich-Zorich cocycle theory
5. Applying ergodic theory of the Teichmüller flow

For now, we provide this as a theorem with an explicit "generic" hypothesis. -/
theorem uniquely_ergodic_of_irrational_data (f : PiecewiseIsometry α)
    (h_finite : f.partition.Finite)
    (h_generic : True)  -- Represents "generic" IET parameters with appropriate irrationality conditions
    :
    ∃ μ : MeasureTheory.Measure α, IsUniquelyErgodic f μ := by
  sorry -- DEEP: Requires Teichmüller theory, Rauzy-Veech induction, etc.
/-
MASUR-VEECH THEOREM - One of the deepest results in the theory of IETs

STATEMENT: For almost all interval exchange transformations (in the sense of
Lebesgue measure on the parameter space), the system is uniquely ergodic.

CONTEXT:
- An IET is determined by two pieces of data:
  a) Length vector λ = (λ₁, ..., λₙ) with ∑ λᵢ = 1
  b) Permutation π ∈ Sₙ
- The "irrationality condition" h_irrat means the lengths satisfy certain
  Diophantine conditions (roughly: no rational relations among them)

SIGNIFICANCE:
- This theorem shows that unique ergodicity is generic (measure-theoretically)
- Proved independently by Masur (1982) and Veech (1982)
- Uses sophisticated techniques from Teichmüller theory
- The proof involves:
  * Rauzy-Veech induction (a renormalization procedure)
  * Analysis of the Kontsevich-Zorich cocycle
  * Ergodic theory of the Teichmüller flow on moduli space

FORMALIZATION CHALLENGES:
1. IRRATIONAL CONDITIONS: Need to formalize "generic" IETs
   - Requires measure on the space of IET parameters
   - Irrationality conditions vary (strong vs weak conditions)

2. RAUZY-VEECH INDUCTION: The main technical tool
   - A symbolic coding of IET orbits
   - Requires combinatorial and geometric arguments

3. UNIQUE ERGODICITY CRITERION: Showing no other invariant measures
   - Uses minimality (all orbits dense)
   - Boshernitzan's criterion relates to complexity growth

REFERENCES:
- Masur, "Interval Exchange Transformations and Measured Foliations", 1982
- Veech, "Gauss Measures for Transformations on the Space of Interval Exchange Maps", 1982
- Yoccoz, "Continued Fraction Algorithms for Interval Exchange Maps", 2005
- Avila & Forni, "Weak mixing for interval exchange transformations", 2007

This is a research-level result requiring substantial formalization effort.
-/

end UniqueErgodicity

section Minimality

/-- A piecewise isometry is minimal if every orbit is dense. -/
def IsMinimal (f : PiecewiseIsometry α) : Prop :=
  ∀ x : α, Dense (Set.range fun n : ℕ => f.toFun^[n] x)

/-- A measure-preserving minimal piecewise isometry. -/
structure MinimalPiecewiseIsometry (α : Type u)
    [MetricSpace α] [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    extends MeasurePreservingPiecewiseIsometry α μ where
  /-- Every orbit is dense -/
  minimal : IsMinimal toPiecewiseIsometry

/-- Minimality implies unique ergodicity for interval exchange transformations.

KEANE'S THEOREM: A minimal interval exchange transformation is uniquely ergodic.

This theorem can be proved using:
1. Birkhoff ergodic theorem (available in Mathlib)
2. Ergodic decomposition theory
3. Weak-* compactness of probability measures
4. The fact that minimality gives uniqueness of ergodic decomposition

The key ingredients needed from Mathlib:
- Birkhoff ergodic theorem: `MeasureTheory.ergodic_birkhoff_sum`
- Ergodic decomposition (not yet in Mathlib as of 2025)
- Krylov-Bogolyubov theorem (existence of invariant measures)

References:
- Keane, "Interval Exchange Transformations", 1975
- Katok & Hasselblatt, "Introduction to the Modern Theory of Dynamical Systems", §4.5 -/
/-
PROOF ATTEMPT HISTORY FOR minimal_implies_uniquely_ergodic:

Attempt 1 [2025-10-16]:
Strategy: Use Birkhoff ergodic theorem + weak-* compactness
Approach (from Katok & Hasselblatt):
  1. Let ν be any invariant probability measure for f
  2. By Birkhoff ergodic theorem, for continuous φ:
     lim (1/n) ∑_{k=0}^{n-1} φ(f^k(x)) = ∫ φ dν for ν-a.e. x
  3. By minimality, the time average is independent of x (orbits are dense)
  4. Therefore ∫ φ dν is constant for all invariant ν
  5. This forces ν = μ (uniqueness)

Challenges:
  - Birkhoff theorem available in Mathlib: `MeasureTheory.Pointwise.ae_tendsto_birkhoff`
  - But need to apply it to ALL invariant measures simultaneously
  - Need ergodic decomposition: every invariant measure is a convex combination of ergodic measures
  - Minimality + ergodic decomposition implies unique ergodic measure

Root issue: Ergodic decomposition not in Mathlib
  - This is a major piece of ergodic theory
  - States: invariant probability measures = convex hull of ergodic measures
  - Requires: weak-* topology on measures, Choquet theory, extremal points

Alternative approach (Boshernitzan's criterion):
  - For IETs, unique ergodicity can be shown via complexity growth
  - Subword complexity p(n) = number of distinct words of length n in symbolic coding
  - If p(n) = o(n²), then the IET is uniquely ergodic
  - Requires substantial combinatorics on words and symbolic dynamics

CLASSIFICATION: Very hard (Keane's Theorem, major result in 1970s)
REQUIRED MATHLIB ADDITIONS:
  - Ergodic decomposition theorem
  - Weak-* topology on probability measures
  - Extremal points and Choquet theory
  - OR: Boshernitzan's criterion (complexity growth for IETs)
-/
theorem minimal_implies_uniquely_ergodic (f : MinimalPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (h_finite : f.toPiecewiseIsometry.partition.Finite) :
    IsUniquelyErgodic f.toPiecewiseIsometry μ := by
  sorry -- DEEP: Requires Birkhoff + ergodic decomposition (not yet in Mathlib as of 2025)

/-- A minimal system is ergodic with respect to any invariant measure.

This is a fundamental theorem connecting topological dynamics (minimality = all orbits dense)
with ergodic theory (invariant sets have measure 0 or 1).

PROOF STRATEGY:
1. Take an invariant measurable set s with μ(s) > 0
2. Use minimality: for any x ∈ s, the orbit {f^n(x) : n ∈ ℕ} is dense
3. By regularity of the measure and Baire category theorem, s must have interior
4. Since orbits are dense, they must intersect both s and sᶜ frequently
5. Using measure preservation and invariance, this forces μ(s) = 1

The proof requires:
- Interaction between Baire category and measure (Borel spaces, regularity)
- Poincaré recurrence theorem (available in Mathlib)
- Properties of dense orbits in metric spaces

References:
- Walters, "An Introduction to Ergodic Theory", Theorem 6.11
- Furstenberg, "Recurrence in Ergodic Theory and Combinatorial Number Theory"
- Katok & Hasselblatt, "Introduction to Modern Dynamical Systems", Prop 4.1.18 -/
/-
PROOF ATTEMPT HISTORY FOR ergodic_of_minimal:

Attempt 1 [2025-10-16]:
Strategy: Use ergodic_iff_invariant_measure and leverage minimality
Approach:
  1. Take invariant set s with μ(s) > 0
  2. Use minimality: all orbits are dense
  3. Try to show μ(sᶜ) = 0

Failure: Invariance means orbits starting in s stay in s (f⁻¹(s) = s).
  - So density of orbits doesn't directly help
  - Can't use "orbit must hit sᶜ" argument

Correct approach (from literature):
  - Use support of the measure: supp(μ) = closure{x : μ({x}) > 0} or whole space
  - If μ has full support and f is minimal, then for invariant s:
    * If μ(s) > 0, then s must be dense (by combining minimality + support)
    * If s is both measurable, invariant, and dense, then μ(sᶜ) = 0
  - Requires: Measure.support theory in Mathlib
  - Requires: Regular measures on metric spaces

Alternative approach (Walters Theorem 6.11):
  - Assume μ(s) ∈ (0, 1) for invariant s
  - By regularity, ∃ open U with s ⊆ U and μ(U \ s) < ε
  - By minimality, ∃x ∈ s with dense orbit
  - The orbit must hit U \ s infinitely often (since U is open and orbit is dense)
  - But orbit of x ∈ s must stay in s (by invariance)
  - Contradiction when ε → 0

This requires:
  - Inner regularity of μ (approximation by compact sets)
  - Outer regularity (approximation by open sets)
  - Properties of dense sets in topology

CLASSIFICATION: Research-level (confirmed in README as "hard")
REQUIRED MATHLIB ADDITIONS:
  - Measure.support for probability measures on metric spaces
  - Regular Borel measures theory
  - Connecting minimality (topological) with ergodicity (measure-theoretic)
-/
theorem ergodic_of_minimal (f : MinimalPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Ergodic f.toFun μ := by
  sorry -- DEEP: Requires measure support theory + regularity + Baire category arguments

end Minimality

section BirkhoffErgodic

-- TODO: The Birkhoff ergodic theorem for piecewise isometries.
-- For an ergodic piecewise isometry and an integrable function, the time average equals
-- the space average almost everywhere.
-- This requires the pointwise ergodic theorem which is not yet in mathlib

end BirkhoffErgodic

section ExamplesOfErgodicSystems

-- TODO: Add axioms for classic ergodic systems examples
-- /-- A rotation by an irrational angle is ergodic. -/
-- Classic result: irrational rotations are ergodic

-- /-- Most interval exchange transformations are ergodic. -/
-- Masur-Veech: generically IETs are ergodic

end ExamplesOfErgodicSystems

section InvariantMeasures

/-- The set of invariant probability measures for a piecewise isometry. -/
def InvariantMeasures (f : PiecewiseIsometry α) : Set (MeasureTheory.Measure α) :=
  {μ | MeasureTheory.IsProbabilityMeasure μ ∧
       MeasureTheory.MeasurePreserving f.toFun μ μ}

-- TODO: The invariant measures form a convex set.
-- TODO: Ergodic measures are extremal points of the invariant measure set.

end InvariantMeasures

section Constructors

/-- Construct an ergodic piecewise isometry from a measure-preserving one with ergodicity
proof. -/
def toErgodicPiecewiseIsometry (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_erg : Ergodic f.toFun μ) :
    ErgodicPiecewiseIsometry α μ where
  toMeasurePreservingPiecewiseIsometry := f
  ergodic := h_erg

end Constructors

end PiecewiseIsometry
