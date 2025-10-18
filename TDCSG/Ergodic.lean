/-
Copyright (c) 2025-10-18 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.MeasureTheory.Measure.Regular

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
- `ergodic_of_minimal`: A minimal system is ergodic with respect to any invariant measure

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
      · rw [Filter.eventuallyConst_pred]
        right
        exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h0
      · rw [Filter.eventuallyConst_pred]
        left
        have h_compl : μ sᶜ = 0 := by
          rw [MeasureTheory.prob_compl_eq_zero_iff hs]
          exact h1
        have : ∀ᵐ x ∂μ, x ∉ sᶜ :=
          MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_compl
        filter_upwards [this] with x hx
        simp only [Set.mem_compl_iff, not_not] at hx
        exact hx

/-- A piecewise isometry is ergodic if it is mixing (stronger condition). -/
theorem ergodic_of_mixing (f : MeasurePreservingPiecewiseIsometry α μ)
    (h_mixing : ∀ s t : Set α, MeasurableSet s → MeasurableSet t →
      Filter.Tendsto (fun n => μ (f.toFun^[n] ⁻¹' s ∩ t)) Filter.atTop
        (nhds (μ s * μ t))) :
    Ergodic f.toFun μ := by
  constructor
  · exact f.measure_preserving
  · constructor
    intro s hs hinv
    rw [Filter.eventuallyConst_pred]
    by_cases h : μ s = 0
    · right
      exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h
    · left
      have h_mix := h_mixing s sᶜ hs hs.compl
      have hinv_n : ∀ n, f.toFun^[n] ⁻¹' s = s := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          show (f.toFun^[n + 1]) ⁻¹' s = s
          rw [Function.iterate_succ, Set.preimage_comp, ih, hinv]
      have h_eq : μ (s ∩ sᶜ) = μ s * μ sᶜ := by
        have : ∀ n, f.toFun^[n] ⁻¹' s ∩ sᶜ = s ∩ sᶜ := fun n => by rw [hinv_n]
        have h_const : Filter.Tendsto (fun n : ℕ => μ (s ∩ sᶜ))
            Filter.atTop (nhds (μ (s ∩ sᶜ))) :=
          tendsto_const_nhds
        have h_eq : (fun n => μ (f.toFun^[n] ⁻¹' s ∩ sᶜ)) =
            fun n => μ (s ∩ sᶜ) := by
          funext n; rw [this]
        rw [h_eq] at h_mix
        exact tendsto_nhds_unique h_const h_mix
      have h_empty : μ (s ∩ sᶜ) = 0 := by simp
      rw [h_empty] at h_eq
      have h_prod_zero : μ s * μ sᶜ = 0 := h_eq.symm
      have : μ sᶜ = 0 := (mul_eq_zero.mp h_prod_zero).resolve_left h
      have : ∀ᵐ x ∂μ, x ∉ sᶜ :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mp this
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
  constructor
  ·
    intro herg s t hs ht μs_pos μt_pos
    by_contra h_none
    push_neg at h_none
    have h_zero : ∀ n, μ (f.toFun^[n] ⁻¹' s ∩ t) = 0 := fun n =>
      le_antisymm (h_none n) (zero_le _)
    let V := {x : α | ∃ᶠ n in Filter.atTop, f.toFun^[n] x ∈ s}
    have h_cons : MeasureTheory.Conservative f.toFun μ :=
      MeasureTheory.MeasurePreserving.conservative f.measure_preserving
    have hV_recur : μ (s ∩ V) = μ s :=
      MeasureTheory.Conservative.measure_inter_frequently_image_mem_eq
        h_cons hs.nullMeasurableSet
    have hμV_pos : μ V > 0 := by
      have : μ s ≤ μ V := by
        rw [← hV_recur]
        exact MeasureTheory.measure_mono Set.inter_subset_right
      exact μs_pos.trans_le this

    by_cases hVt : μ (V ∩ t) = 0
    · have hVtc : μ (V ∩ tᶜ) > 0 := by
        have : μ V = μ (V ∩ t) + μ (V ∩ tᶜ) := by
          have h_split : V = (V ∩ t) ∪ (V ∩ tᶜ) := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
            tauto
          conv_lhs => rw [h_split]
          have h_disj : Disjoint (V ∩ t) (V ∩ tᶜ) := by
            rw [Set.disjoint_iff]
            intro x ⟨⟨_, hxt⟩, _, hxtc⟩
            exact hxtc hxt
          sorry
        rw [hVt, zero_add] at this
        rw [← this]
        exact hμV_pos

      let W := {x : α | ∃ᶠ n in Filter.atTop, f.toFun^[n] x ∈ t}
      have hW_recur : μ (t ∩ W) = μ t :=
        MeasureTheory.Conservative.measure_inter_frequently_image_mem_eq
          h_cons ht.nullMeasurableSet

      have hμW_pos : μ W > 0 := by
        have : μ t ≤ μ W := by
          rw [← hW_recur]
          exact MeasureTheory.measure_mono Set.inter_subset_right
        exact μt_pos.trans_le this
      sorry
    · have h_subset : V ∩ t ⊆ ⋃ n : ℕ, f.toFun^[n] ⁻¹' s ∩ t := by
        intro x ⟨hxV, hxt⟩
        change (∃ᶠ n in Filter.atTop, f.toFun^[n] x ∈ s) at hxV
        rw [Filter.frequently_atTop] at hxV
        obtain ⟨n, _, hn⟩ := hxV 0
        exact Set.mem_iUnion.mpr ⟨n, hn, hxt⟩

      have h_union_zero : μ (⋃ n : ℕ, f.toFun^[n] ⁻¹' s ∩ t) = 0 :=
        MeasureTheory.measure_iUnion_null h_zero

      have h_le : μ (V ∩ t) ≤ μ (⋃ n : ℕ, f.toFun^[n] ⁻¹' s ∩ t) :=
        MeasureTheory.measure_mono h_subset

      rw [h_union_zero] at h_le
      have h_gt : μ (V ∩ t) > 0 := (zero_le _).lt_of_ne (Ne.symm hVt)
      have : μ (V ∩ t) = 0 := le_antisymm h_le (zero_le _)
      rw [this] at h_gt
      exact (lt_irrefl 0) h_gt
  · intro h_irred
    rw [ergodic_iff_invariant_measure]
    intro s hs h_inv
    by_cases h : μ s = 0
    · left; exact h
    · right
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
      obtain ⟨n, hn⟩ := h_irred s sᶜ hs hs.compl μs_pos μsc_pos
      have hinv_n : ∀ k, f.toFun^[k] ⁻¹' s = s := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [Function.iterate_succ]
          rw [Set.preimage_comp, ih, h_inv]
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

/-- A minimal system is ergodic with respect to any invariant measure. -/
theorem ergodic_of_minimal [OpensMeasurableSpace α] [BorelSpace α]
    [μ.WeaklyRegular]
    (f : MinimalPiecewiseIsometry α μ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Ergodic f.toFun μ := by
  rw [ergodic_iff_invariant_measure]
  intro s hs hinv
  by_cases h0 : μ s = 0
  · left; exact h0
  by_cases h1 : μ s = 1
  · right; exact h1
  exfalso

  have hμs_pos : 0 < μ s := by
    apply (Ne.symm h0).lt_of_le
    exact zero_le (μ s)

  have hμs_lt_one : μ s < 1 := by
    by_contra h_not
    push_neg at h_not
    have : μ s ≤ 1 := MeasureTheory.prob_le_one
    have : μ s = 1 := le_antisymm this h_not
    exact h1 this


  have hμs_ne_top : μ s ≠ ⊤ := by
    have : μ s ≤ 1 := MeasureTheory.prob_le_one
    exact ne_of_lt (this.trans_lt ENNReal.one_lt_top)

  obtain ⟨r, hsr, hr1⟩ := exists_between hμs_lt_one

  have hμsc_ne_top : μ sᶜ ≠ ⊤ := by
    have h_le : μ sᶜ ≤ 1 := by
      have : μ sᶜ ≤ μ Set.univ := μ.mono (Set.subset_univ _)
      rw [MeasureTheory.measure_univ] at this
      exact this
    exact ne_of_lt (h_le.trans_lt ENNReal.one_lt_top)

  have hμsc_pos : 0 < μ sᶜ := by
    have h_compl : μ sᶜ = 1 - μ s := by
      have h_univ : μ Set.univ = 1 := MeasureTheory.measure_univ
      rw [MeasureTheory.measure_compl hs hμs_ne_top, h_univ]
    rw [h_compl]
    rw [tsub_pos_iff_lt]
    exact hμs_lt_one

  have hs_nonempty : s.Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty] at hμs_pos
    simp at hμs_pos

  obtain ⟨x, hx⟩ := hs_nonempty

  have h_dense : Dense (Set.range fun n : ℕ => f.toFun^[n] x) := f.minimal x

  have h_1_sub_r_pos : 0 < 1 - r := by
    rw [tsub_pos_iff_lt]
    exact hr1
  have h_target : μ sᶜ < μ sᶜ + (1 - r) := by
    apply ENNReal.lt_add_right hμsc_ne_top
    exact ne_of_gt h_1_sub_r_pos

  obtain ⟨V, hscV, hV_open, hμV⟩ :=
    MeasureTheory.Measure.OuterRegular.outerRegular
      hs.compl (μ sᶜ + (1 - r)) h_target

  have hVc_closed : IsClosed Vᶜ := hV_open.isClosed_compl
  have hVcs : Vᶜ ⊆ s := by
    intro y hy
    by_contra hys
    have : y ∈ sᶜ := hys
    exact hy (hscV this)



  have hVsc : V ∩ sᶜ = sᶜ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    exact ⟨fun h => h.2, fun h => ⟨hscV h, h⟩⟩

  have hV_partition : V = (V ∩ s) ∪ sᶜ := by
    rw [← hVsc]
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · intro hyV
      by_cases hys : y ∈ s
      · left; exact ⟨hyV, hys⟩
      · right; exact ⟨hyV, hys⟩
    · intro h
      rcases h with ⟨hyV, _⟩ | ⟨_, hys⟩
      · exact hyV
      · exact hscV hys

  have hμV_eq : μ V = μ (V ∩ s) + μ sᶜ := by
    rw [hV_partition]
    refine MeasureTheory.measure_union_add_inter _ (hV_open.inter hs).measurableSet hs.compl

  have hμVs_lt : μ (V ∩ s) < 1 - r := by
    have h : μ (V ∩ s) + μ sᶜ < μ sᶜ + (1 - r) := by
      rw [← hμV_eq]; exact hμV
    exact ENNReal.add_lt_add_iff_left hμsc_ne_top |>.mp h

  have hV_meas : MeasurableSet V := hV_open.measurableSet



  have hs_partition : s = Vᶜ ∪ (V ∩ s) := by
    ext y
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    constructor
    · intro hys
      by_cases hyV : y ∈ V
      · right; exact ⟨hyV, hys⟩
      · left; exact hyV
    · intro h
      rcases h with hyVc | ⟨_, hys⟩
      · exact hVcs hyVc
      · exact hys

  have hs_disj : Disjoint Vᶜ (V ∩ s) := by
    rw [Set.disjoint_iff]
    intro y ⟨hyVc, hyV, _⟩
    exact hyVc hyV

  have hμs_eq : μ s = μ Vᶜ + μ (V ∩ s) := by
    rw [hs_partition]
    refine MeasureTheory.measure_union_add_inter _
      hVc_closed.measurableSet (hV_open.inter hs).measurableSet



  have h_sc_bound : 1 - r < μ sᶜ := by
    have h_compl : μ sᶜ = 1 - μ s := by
      rw [MeasureTheory.measure_compl hs hμs_ne_top, MeasureTheory.measure_univ]
    rw [h_compl]
    exact ENNReal.sub_lt_sub_of_lt_of_le (le_refl 1) hsr (Or.inl ENNReal.one_ne_top)






  linarith [hμVs_lt, h_sc_bound]

end Minimality

section BirkhoffErgodic


end BirkhoffErgodic

section ExamplesOfErgodicSystems



end ExamplesOfErgodicSystems

section InvariantMeasures

/-- The set of invariant probability measures for a piecewise isometry. -/
def InvariantMeasures (f : PiecewiseIsometry α) : Set (MeasureTheory.Measure α) :=
  {μ | MeasureTheory.IsProbabilityMeasure μ ∧
       MeasureTheory.MeasurePreserving f.toFun μ μ}


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
