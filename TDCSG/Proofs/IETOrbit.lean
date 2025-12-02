/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Proofs.Word1Correspondence
import TDCSG.Proofs.Word2Correspondence
import TDCSG.Proofs.Word3Correspondence
import TDCSG.Proofs.IET
import TDCSG.Proofs.Orbit
import TDCSG.Proofs.OrbitInfinite
import TDCSG.Definitions.IET

/-!
# IET Orbit Correspondence

This file establishes the correspondence between the interval exchange transformation (IET)
dynamics and the group orbit under the compound symmetry group, proving that an infinite IET
orbit implies an infinite group orbit.

## Main results

- `IET_step_word_correspondence`: Single IET step corresponds to applying a word to the segment
- `wordForIterate_correct`: Iterating the IET corresponds to applying accumulated words
- `IET_orbit_subset_group_orbit`: IET orbit points lie in the group orbit
- `IET_orbit_infinite_implies_group_orbit_infinite`: Infinite IET orbit implies infinite group orbit

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real CompoundSymmetry.GG5
open TDCSG.Definitions

lemma IET_toFun_interval0 (x : ℝ) (hx_lo : 0 ≤ x) (hx_hi : x < length1) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun x = x + displacement0 := by
  have hx_mem : x ∈ Set.Ico 0 1 := by
    constructor
    · exact hx_lo
    · calc x < length1 := hx_hi
           _ < 1 := length1_lt_one
  have h := CompoundSymmetry.GG5.GG5_displacement_eq_toFun_sub x hx_mem
  unfold CompoundSymmetry.GG5.GG5_displacement at h
  simp only [hx_hi, if_true] at h
  linarith

lemma IET_toFun_interval1 (x : ℝ) (hx_lo : length1 ≤ x)
    (hx_hi : x < length1 + length2) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun x = x + displacement1 := by
  have hx_mem : x ∈ Set.Ico 0 1 := by
    constructor
    · calc 0 ≤ length1 := le_of_lt length1_pos
           _ ≤ x := hx_lo
    · calc x < length1 + length2 := hx_hi
           _ < 1 := length12_lt_one
  have h := CompoundSymmetry.GG5.GG5_displacement_eq_toFun_sub x hx_mem
  unfold CompoundSymmetry.GG5.GG5_displacement at h
  have h_not_0 : ¬(x < length1) := not_lt.mpr hx_lo
  simp only [h_not_0, if_false, hx_hi, if_true] at h
  linarith

lemma IET_toFun_interval2 (x : ℝ)
    (hx_lo : length1 + length2 ≤ x) (hx_hi : x < 1) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun x = x + displacement2 := by
  have hx_mem : x ∈ Set.Ico 0 1 := by
    constructor
    · calc 0 ≤ length1 + length2 := by
            have h1 := length1_pos
            have h2 := length2_pos
            linarith
           _ ≤ x := hx_lo
    · exact hx_hi
  have h := CompoundSymmetry.GG5.GG5_displacement_eq_toFun_sub x hx_mem
  unfold CompoundSymmetry.GG5.GG5_displacement at h
  have h_not_0 : ¬(x < length1) := by
    push_neg
    calc length1 ≤ length1 + length2 := by
          have h2 := length2_pos
          linarith
         _ ≤ x := hx_lo
  have h_not_1 : ¬(x < length1 + length2) := not_lt.mpr hx_lo
  simp only [h_not_0, if_false, h_not_1, if_false] at h
  linarith

theorem IET_step_word_correspondence (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    applyWord r_crit (IET_word x) (segmentPoint x) =
    segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun x) := by

  unfold IET_word
  by_cases h0 : x < length1
  ·
    simp only [h0, ↓reduceIte]

    rw [word1_produces_displacement0 x hx h0]
    congr 1
    exact (IET_toFun_interval0 x hx.1 h0).symm
  · simp only [h0, ↓reduceIte]
    by_cases h1 : x < length1 + length2
    ·
      simp only [h1, ↓reduceIte]

      rw [word2_produces_displacement1 x hx (le_of_not_gt h0) h1]
      congr 1
      exact (IET_toFun_interval1 x (le_of_not_gt h0) h1).symm
    ·
      simp only [h1, ↓reduceIte]

      rw [word3_produces_displacement2 x hx (le_of_not_gt h1)]
      congr 1
      exact (IET_toFun_interval2 x (le_of_not_gt h1) hx.2).symm

theorem IET_iterate_mem_Ico (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1) (n : ℕ) :
    CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀ ∈ Set.Ico 0 1 := by
  induction n with
  | zero => simp [hx₀]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact CompoundSymmetry.GG5.GG5_IET_maps_to_self _ ih

theorem wordForIterate_correct (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1) (n : ℕ) :
    applyWord r_crit (wordForIterate x₀ n) (segmentPoint x₀) =
    segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀) := by
  induction n with
  | zero =>

    simp only [Function.iterate_zero, id_eq, wordForIterate, applyWord, List.foldl_nil]
  | succ n ih =>

    simp only [Function.iterate_succ', Function.comp_apply]
    rw [wordForIterate, applyWord, List.foldl_append]

    have h_inner : List.foldl (applyGen r_crit) (segmentPoint x₀) (wordForIterate x₀ n) =
        applyWord r_crit (wordForIterate x₀ n) (segmentPoint x₀) := rfl
    rw [h_inner, ih]

    have h_outer : List.foldl (applyGen r_crit)
        (segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀))
        (IET_word (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀)) =
        applyWord r_crit (IET_word (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀))
        (segmentPoint (CompoundSymmetry.GG5.GG5_induced_IET.toFun^[n] x₀)) := rfl
    rw [h_outer]
    exact IET_step_word_correspondence _ (IET_iterate_mem_Ico x₀ hx₀ n)

theorem IET_orbit_subset_group_orbit (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1) :
    ∀ y ∈ RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀,
      ∃ w : Word, applyWord r_crit w (segmentPoint x₀) = segmentPoint y := by
  intro y hy
  rw [RealDynamics.orbitSet] at hy
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨n, hn⟩ := hy
  use wordForIterate x₀ n
  rw [← hn]
  exact wordForIterate_correct x₀ hx₀ n

theorem IET_orbit_infinite_implies_group_orbit_infinite (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ico 0 1)
    (h_inf : (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀).Infinite) :
    (orbit r_crit (segmentPoint x₀)).Infinite := by

  have h_subset : segmentPoint '' (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀) ⊆
      orbit r_crit (segmentPoint x₀) := by
    intro p hp
    rw [Set.mem_image] at hp
    obtain ⟨y, hy_mem, hy_eq⟩ := hp
    rw [orbit]
    simp only [Set.mem_setOf_eq]
    obtain ⟨w, hw⟩ := IET_orbit_subset_group_orbit x₀ hx₀ y hy_mem
    use w
    rw [← hy_eq, hw]

  have h_inj : Set.InjOn segmentPoint (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀) := by
    intro y₁ _ y₂ _ h
    exact segmentPoint_injective h
  have h_image_inf : (segmentPoint '' (RealDynamics.orbitSet CompoundSymmetry.GG5.GG5_induced_IET.toFun x₀)).Infinite :=
    Set.Infinite.image h_inj h_inf
  exact Set.Infinite.mono h_subset h_image_inf

end TDCSG.CompoundSymmetry.GG5
