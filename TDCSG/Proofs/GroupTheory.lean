/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.GroupTheory
import TDCSG.Proofs.IETOrbit
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finite.Defs

/-!
# Compound Symmetry Group - Proofs

This file proves the key properties connecting the group-theoretic definition
to the existing orbit infrastructure, culminating in the proof that an infinite
orbit implies an infinite group.

## Main Results

- `genA_order_five` : A⁵ = 1 (generator A has order 5)
- `genB_order_five` : B⁵ = 1 (generator B has order 5)
- `orbit_eq_groupOrbit` : The word-based orbit equals the MulAction orbit
- `infinite_orbit_implies_infinite_group` : ∃ p, (orbit r p).Infinite → (CompoundSymmetryGroup r).Infinite

## Proof Strategy

1. Prove generators have order 5, hence are bijections
2. Show word-based orbit equals MulAction.orbit for the subgroup
3. Use contrapositive of `Finite.finite_mulAction_orbit`: infinite orbit ⟹ infinite group
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions
open scoped Complex

/-! ### Generator Order -/

/-- Circle.exp θ ^ n = Circle.exp (n * θ). -/
private lemma Circle_exp_pow (θ : ℝ) (n : ℕ) : Circle.exp θ ^ n = Circle.exp (n * θ) := by
  induction n with
  | zero => simp [Circle.exp_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← Circle.exp_add]
    congr 1
    push_cast
    ring

/-- Circle.exp (-2π) = 1, the fundamental periodicity. -/
private lemma circle_exp_neg_two_pi : Circle.exp (-2 * Real.pi) = 1 := by
  apply Subtype.ext
  simp only [Circle.coe_exp, Circle.coe_one]
  push_cast
  have h : (-2 : ℂ) * ↑Real.pi * Complex.I = -(2 * ↑Real.pi * Complex.I) := by ring
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- 5 rotations by -2π/5 = identity (key for order 5). -/
private lemma Circle_exp_neg_two_pi_over_5_pow_5 : Circle.exp (-2 * Real.pi / 5) ^ 5 = 1 := by
  rw [Circle_exp_pow]
  have h : (5 : ℕ) * (-2 * Real.pi / 5) = -2 * Real.pi := by ring
  rw [h]
  exact circle_exp_neg_two_pi

/-- genA acts as identity outside the left disk. -/
private lemma genA_outside (r : ℝ) (z : ℂ) (hz : z ∉ leftDisk r) : genA r z = z := by
  unfold genA
  simp only [hz, ↓reduceIte]

/-- genA acts as rotation inside the left disk. -/
private lemma genA_inside (r : ℝ) (z : ℂ) (hz : z ∈ leftDisk r) :
    genA r z = rotateAboutCircle leftCenter (Circle.exp (-2 * Real.pi / 5)) z := by
  unfold genA
  simp only [hz, ↓reduceIte]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- Rotation about leftCenter preserves leftDisk membership. -/
private lemma rotateAboutCircle_leftCenter_preserves_leftDisk (a : Circle) (r : ℝ) (z : ℂ)
    (hz : z ∈ leftDisk r) : rotateAboutCircle leftCenter a z ∈ leftDisk r := by
  unfold leftDisk
  have h_center : leftCenter = (-1 : ℂ) := by unfold leftCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk (-1) a r z hz

/-- Generator A has order 5: applying it 5 times gives the identity. -/
lemma genA_pow_five (r : ℝ) (z : ℂ) :
    genA r (genA r (genA r (genA r (genA r z)))) = z := by
  by_cases hz : z ∈ leftDisk r
  · -- Inside case: 5 rotations = identity
    set a := Circle.exp (-2 * Real.pi / 5) with ha
    set rot := rotateAboutCircle leftCenter a with hrot
    -- Each genA application preserves disk membership and equals rotation
    have step1 : genA r z = rot z := genA_inside r z hz
    have mem1 : rot z ∈ leftDisk r := rotateAboutCircle_leftCenter_preserves_leftDisk a r z hz
    have step2 : genA r (rot z) = rot (rot z) := genA_inside r (rot z) mem1
    have mem2 : rot (rot z) ∈ leftDisk r := rotateAboutCircle_leftCenter_preserves_leftDisk a r _ mem1
    have step3 : genA r (rot (rot z)) = rot (rot (rot z)) := genA_inside r _ mem2
    have mem3 : rot (rot (rot z)) ∈ leftDisk r := rotateAboutCircle_leftCenter_preserves_leftDisk a r _ mem2
    have step4 : genA r (rot (rot (rot z))) = rot (rot (rot (rot z))) := genA_inside r _ mem3
    have mem4 : rot (rot (rot (rot z))) ∈ leftDisk r := rotateAboutCircle_leftCenter_preserves_leftDisk a r _ mem3
    have step5 : genA r (rot (rot (rot (rot z)))) = rot (rot (rot (rot (rot z)))) := genA_inside r _ mem4
    -- Chain together: 5 genA applications = 5 rotations = rotation by power 5
    calc genA r (genA r (genA r (genA r (genA r z))))
        = genA r (genA r (genA r (genA r (rot z)))) := by rw [step1]
      _ = genA r (genA r (genA r (rot (rot z)))) := by rw [step2]
      _ = genA r (genA r (rot (rot (rot z)))) := by rw [step3]
      _ = genA r (rot (rot (rot (rot z)))) := by rw [step4]
      _ = rot (rot (rot (rot (rot z)))) := by rw [step5]
      _ = rotateAboutCircle leftCenter (a * (a * (a * (a * a)))) z := by
          simp only [hrot, ← rotateAboutCircle_mul]
      _ = rotateAboutCircle leftCenter (a ^ 5) z := by
          congr 1; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = rotateAboutCircle leftCenter 1 z := by rw [ha, Circle_exp_neg_two_pi_over_5_pow_5]
      _ = z := rotateAboutCircle_one leftCenter z
  · -- Outside case: genA is identity
    simp only [genA_outside r z hz]

/-- Generator B has order 5: applying it 5 times gives the identity. -/
lemma genB_pow_five (r : ℝ) (z : ℂ) :
    genB r (genB r (genB r (genB r (genB r z)))) = z := by
  -- Case split on whether z is in the right disk
  by_cases hz : z ∈ rightDisk r
  · -- Inside disk: 5 rotations by -2π/5 = rotation by -2π = identity
    -- First show that genB preserves membership in rightDisk
    have h1 : genB r z ∈ rightDisk r := genB_preserves_rightDisk r z hz
    have h2 : genB r (genB r z) ∈ rightDisk r := genB_preserves_rightDisk r (genB r z) h1
    have h3 : genB r (genB r (genB r z)) ∈ rightDisk r :=
      genB_preserves_rightDisk r (genB r (genB r z)) h2
    have h4 : genB r (genB r (genB r (genB r z))) ∈ rightDisk r :=
      genB_preserves_rightDisk r (genB r (genB r (genB r z))) h3
    -- Define the rotation element
    set ω := Circle.exp (-2 * Real.pi / 5) with hω_def
    -- Rewrite the goal step by step, from outermost to innermost
    -- First, use the fact that genB on rightDisk = rotation
    calc genB r (genB r (genB r (genB r (genB r z))))
        = rotateAboutCircle rightCenter ω (genB r (genB r (genB r (genB r z)))) :=
          genB_in_disk_eq_rotateAboutCircle r _ h4
      _ = rotateAboutCircle rightCenter ω (rotateAboutCircle rightCenter ω (genB r (genB r (genB r z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r _ h3]
      _ = rotateAboutCircle rightCenter ω (rotateAboutCircle rightCenter ω
            (rotateAboutCircle rightCenter ω (genB r (genB r z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r _ h2]
      _ = rotateAboutCircle rightCenter ω (rotateAboutCircle rightCenter ω
            (rotateAboutCircle rightCenter ω (rotateAboutCircle rightCenter ω (genB r z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r _ h1]
      _ = rotateAboutCircle rightCenter ω (rotateAboutCircle rightCenter ω
            (rotateAboutCircle rightCenter ω (rotateAboutCircle rightCenter ω
              (rotateAboutCircle rightCenter ω z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r z hz]
      _ = rotateAboutCircle rightCenter (ω ^ 5) z := by
          -- Use rotateAboutCircle_pow to collapse 5 nested rotations
          have h_iter : (rotateAboutCircle rightCenter ω)^[5] z =
              rotateAboutCircle rightCenter (ω ^ 5) z := rotateAboutCircle_pow rightCenter ω 5 z
          simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply] at h_iter
          exact h_iter
      _ = rotateAboutCircle rightCenter 1 z := by
          -- Show ω^5 = 1
          have omega_pow_five : ω ^ 5 = 1 := by
            rw [hω_def]
            ext
            rw [SubmonoidClass.coe_pow, Circle.coe_exp, Circle.coe_one]
            rw [← Complex.exp_nat_mul]
            -- The goal is: cexp (↑5 * (↑(-2 * Real.pi / 5) * Complex.I)) = 1
            -- Need to show 5 * (↑(-2 * Real.pi / 5) * I) = -1 * (2π * I)
            have h_eq : (5 : ℕ) * (((-2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
                (-1 : ℤ) * (2 * Real.pi * Complex.I) := by
              push_cast
              ring
            rw [h_eq, Complex.exp_int_mul_two_pi_mul_I]
          rw [omega_pow_five]
      _ = z := rotateAboutCircle_one rightCenter z
  · -- Outside disk: genB is the identity, so z stays z at each step
    have hgenB_id : ∀ w, w ∉ rightDisk r → genB r w = w := fun w hw => by
      unfold genB
      simp only [hw, ↓reduceIte]
    -- z ∉ rightDisk r, so genB r z = z
    rw [hgenB_id z hz]
    -- Now z ∉ rightDisk r implies genB r z = z, so we just have z
    rw [hgenB_id z hz, hgenB_id z hz, hgenB_id z hz, hgenB_id z hz]

/-- genA_perm has order 5 in the group Equiv.Perm ℂ. -/
lemma genA_perm_pow_five (r : ℝ) : genA_perm r ^ 5 = 1 := by
  ext z
  simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
             Function.comp_apply, Equiv.Perm.coe_one, id_eq, genA_perm_apply]
  exact genA_pow_five r z

/-- genB_perm has order 5 in the group Equiv.Perm ℂ. -/
lemma genB_perm_pow_five (r : ℝ) : genB_perm r ^ 5 = 1 := by
  ext z
  simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
             Function.comp_apply, Equiv.Perm.coe_one, id_eq, genB_perm_apply]
  exact genB_pow_five r z

/-! ### Orbit Equivalence -/

/-- Convert a generator to the corresponding permutation in TwoDiskCompoundSymmetryGroup. -/
private noncomputable def genToPerm (r : ℝ) : Generator → TwoDiskCompoundSymmetryGroup r
  | .A => ⟨genA_perm r, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  | .Ainv => ⟨(genA_perm r)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))⟩
  | .B => ⟨genB_perm r, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  | .Binv => ⟨(genB_perm r)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

/-- The action of genToPerm agrees with applyGen. -/
private lemma genToPerm_action (r : ℝ) (g : Generator) (p : ℂ) :
    (genToPerm r g).val p = applyGen r p g := by
  cases g with
  | A => simp [genToPerm, applyGen, genA_perm_apply]
  | Ainv =>
    simp only [genToPerm, applyGen]
    have h : (genA_perm r)⁻¹ = (genA_perm r) ^ 4 := by
      have h5 : (genA_perm r) ^ 5 = 1 := genA_perm_pow_five r
      calc (genA_perm r)⁻¹ = (genA_perm r)⁻¹ * 1 := by simp
        _ = (genA_perm r)⁻¹ * (genA_perm r) ^ 5 := by rw [h5]
        _ = (genA_perm r) ^ 4 := by group
    simp only [h, Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
               Function.comp_apply, genA_perm_apply]
    rfl
  | B => simp [genToPerm, applyGen, genB_perm_apply]
  | Binv =>
    simp only [genToPerm, applyGen]
    have h : (genB_perm r)⁻¹ = (genB_perm r) ^ 4 := by
      have h5 : (genB_perm r) ^ 5 = 1 := genB_perm_pow_five r
      calc (genB_perm r)⁻¹ = (genB_perm r)⁻¹ * 1 := by simp
        _ = (genB_perm r)⁻¹ * (genB_perm r) ^ 5 := by rw [h5]
        _ = (genB_perm r) ^ 4 := by group
    simp only [h, Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
               Function.comp_apply, genB_perm_apply]
    rfl

/-- Convert a word to a group element (product of generators from right to left).
    For word [g1, g2, g3], this produces genToPerm g3 * genToPerm g2 * genToPerm g1. -/
private noncomputable def wordToPerm (r : ℝ) : Word → TwoDiskCompoundSymmetryGroup r
  | [] => 1
  | g :: gs => wordToPerm r gs * genToPerm r g

/-- Key lemma: wordToPerm applied to z equals applyWord. -/
private lemma wordToPerm_action (r : ℝ) (w : Word) (p : ℂ) :
    (wordToPerm r w).val p = applyWord r w p := by
  induction w generalizing p with
  | nil =>
    simp only [wordToPerm, applyWord, List.foldl_nil]
    rfl
  | cons g gs ih =>
    simp only [wordToPerm, applyWord, List.foldl_cons]
    -- (wordToPerm r gs * genToPerm r g).val p = List.foldl (applyGen r) (applyGen r p g) gs
    -- LHS = (wordToPerm r gs).val ((genToPerm r g).val p)
    --     = (wordToPerm r gs).val (applyGen r p g)   by genToPerm_action
    --     = applyWord r gs (applyGen r p g)          by ih
    --     = List.foldl (applyGen r) (applyGen r p g) gs   by def of applyWord
    have h1 : (wordToPerm r gs * genToPerm r g).val p =
              (wordToPerm r gs).val ((genToPerm r g).val p) := by
      simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h1, genToPerm_action, ih]
    rfl

/-- Every element reachable by a word is in the MulAction orbit of the subgroup. -/
lemma word_orbit_subset_group_orbit (r : ℝ) (z : ℂ) :
    orbit r z ⊆ groupOrbit r z := by
  intro w hw
  obtain ⟨word, hw_eq⟩ := hw
  rw [groupOrbit, MulAction.mem_orbit_iff]
  use wordToPerm r word
  rw [← hw_eq]
  exact wordToPerm_action r word z

/-- Helper lemma: wordToPerm distributes over append in reverse order. -/
private lemma wordToPerm_append (r : ℝ) (u v : Word) :
    wordToPerm r (u ++ v) = wordToPerm r v * wordToPerm r u := by
  induction u with
  | nil => simp [wordToPerm]
  | cons g gs ih =>
    simp only [List.cons_append, wordToPerm]
    rw [ih]
    group

/-- Helper: every element of the closure has a corresponding word.
    For any g in TwoDiskCompoundSymmetryGroup r, there exists a word w
    such that g.val = (wordToPerm r w).val as permutations. -/
private lemma closure_element_has_word (r : ℝ) (g : TwoDiskCompoundSymmetryGroup r) :
    ∃ w : Word, g.val = (wordToPerm r w).val := by
  obtain ⟨g_perm, hg⟩ := g
  -- Use closure induction with predicate: ∃ w, g_perm = (wordToPerm r w).val
  refine Subgroup.closure_induction (p := fun g _ => ∃ w : Word, g = (wordToPerm r w).val)
    ?mem ?one ?mul ?inv hg
  case mem =>
    -- Generator case: genA_perm or genB_perm
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    cases hx with
    | inl h =>
      -- x = genA_perm r corresponds to word [A]
      use [Generator.A]
      rw [h]
      simp only [wordToPerm, genToPerm, one_mul, Subgroup.coe_mk]
    | inr h =>
      -- x = genB_perm r corresponds to word [B]
      use [Generator.B]
      rw [h]
      simp only [wordToPerm, genToPerm, one_mul, Subgroup.coe_mk]
  case one =>
    -- Identity corresponds to empty word
    use []
    simp only [wordToPerm, Subgroup.coe_one]
  case mul =>
    -- If g corresponds to w₁ and h corresponds to w₂, then g * h corresponds to w₂ ++ w₁
    intro g' h' _ _ ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
    use w₂ ++ w₁
    rw [hw₁, hw₂, wordToPerm_append]
    simp only [Subgroup.coe_mul]
  case inv =>
    -- If g corresponds to w, then g⁻¹ corresponds to reversed word with inverted generators
    intro g' _ ⟨w, hw⟩
    -- Define the inverse of a generator
    let invGen : Generator → Generator
      | .A => .Ainv
      | .Ainv => .A
      | .B => .Binv
      | .Binv => .B
    use (w.reverse.map invGen)
    rw [hw]
    -- Need: ((wordToPerm r w).val)⁻¹ = (wordToPerm r (w.reverse.map invGen)).val
    -- First show that invGen inverts generators at the permutation level
    have h_invGen : ∀ gen, (genToPerm r (invGen gen)).val = ((genToPerm r gen).val)⁻¹ := by
      intro gen
      cases gen <;> simp only [invGen, genToPerm, Subgroup.coe_mk, inv_inv]
    -- Prove the general lemma about word inversion
    have h_rev_inv : ∀ (v : Word),
        (wordToPerm r (v.reverse.map invGen)).val = ((wordToPerm r v).val)⁻¹ := by
      intro v
      induction v with
      | nil =>
        simp only [List.reverse_nil, List.map_nil, wordToPerm, Subgroup.coe_one, inv_one]
      | cons g gs ih =>
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, wordToPerm]
        rw [wordToPerm_append]
        simp only [wordToPerm, one_mul, Subgroup.coe_mul]
        rw [mul_inv_rev, ih, h_invGen]
    rw [← h_rev_inv w]

/-- Every element in the MulAction orbit is reachable by some word. -/
lemma group_orbit_subset_word_orbit (r : ℝ) (z : ℂ) :
    groupOrbit r z ⊆ orbit r z := by
  intro w hw
  rw [groupOrbit, MulAction.mem_orbit_iff] at hw
  obtain ⟨g, hgw⟩ := hw
  -- g is in TwoDiskCompoundSymmetryGroup r, so there exists word w such that g = wordToPerm r w
  obtain ⟨word, hword⟩ := closure_element_has_word r g
  -- w = g • z = g.val z = (wordToPerm r word).val z = applyWord r word z
  use word
  rw [← hgw]
  -- Goal: applyWord r word z = g • z
  -- g • z = g.val z for subgroup elements acting on the type
  -- g.val = (wordToPerm r word).val by hword
  -- (wordToPerm r word).val z = applyWord r word z by wordToPerm_action
  have h2 : (wordToPerm r word).val z = applyWord r word z := wordToPerm_action r word z
  calc applyWord r word z
      = (wordToPerm r word).val z := h2.symm
    _ = g.val z := by rw [← hword]
    _ = g • z := rfl

/-- The word-based orbit equals the group-theoretic MulAction orbit.

    This is the key bridge between the existing proof infrastructure
    (which uses words) and the proper group-theoretic formulation. -/
theorem orbit_eq_groupOrbit (r : ℝ) (z : ℂ) :
    orbit r z = groupOrbit r z := by
  apply Set.eq_of_subset_of_subset
  · exact word_orbit_subset_group_orbit r z
  · exact group_orbit_subset_word_orbit r z

/-! ### Infinite Orbit Implies Infinite Group -/

/-- If the word-based orbit is infinite, the group orbit is infinite. -/
lemma word_orbit_infinite_iff_group_orbit_infinite (r : ℝ) (z : ℂ) :
    (orbit r z).Infinite ↔ (groupOrbit r z).Infinite := by
  rw [orbit_eq_groupOrbit]

/-- Key lemma: If a group action has an infinite orbit, the group is infinite.

    This is the contrapositive of Mathlib's `Finite.finite_mulAction_orbit`:
    if the group were finite, all orbits would be finite. -/
lemma infinite_orbit_implies_infinite_group {G : Type*} [Group G] [MulAction G ℂ]
    (z : ℂ) (h : (MulAction.orbit G z).Infinite) : Infinite G := by
  by_contra hfin
  push_neg at hfin
  haveI : Finite G := hfin
  exact h (Finite.finite_mulAction_orbit z)

/-- The compound symmetry group is infinite if it has a point with infinite orbit. -/
theorem CompoundSymmetryGroup_infinite_of_infinite_orbit (r : ℝ) (z : ℂ)
    (h : (groupOrbit r z).Infinite) : Infinite (TwoDiskCompoundSymmetryGroup r) := by
  exact infinite_orbit_implies_infinite_group z h

/-- GG5 is infinite if it has a point with infinite orbit. -/
theorem GG5_infinite_of_infinite_orbit (z : ℂ)
    (h : (GG5_orbit z).Infinite) : Infinite GG5_At_Critical_radius := by
  exact CompoundSymmetryGroup_infinite_of_infinite_orbit r_crit z h

/-! ### Bridge to Existing Infrastructure -/

/-- The existing proof gives us a point with infinite word-orbit.
    This lifts to infinite group orbit. -/
theorem GG5_has_infinite_group_orbit :
    ∃ z : ℂ, (GG5_orbit z).Infinite := by
  obtain ⟨x₀, hx₀_mem, hx₀_inf⟩ := GG5_IET_has_infinite_orbit
  use segmentPoint x₀
  -- GG5_orbit = MulAction.orbit GG5
  -- Need to show this equals the word-based orbit
  show (MulAction.orbit GG5_At_Critical_radius (segmentPoint x₀)).Infinite
  -- From IETOrbit.lean: IET infinite orbit implies word-based orbit is infinite
  have h_word_inf : (orbit r_crit (segmentPoint x₀)).Infinite :=
    IET_orbit_infinite_implies_group_orbit_infinite x₀ hx₀_mem hx₀_inf
  -- From orbit_eq_groupOrbit: word-based orbit = group orbit (MulAction.orbit)
  rw [orbit_eq_groupOrbit] at h_word_inf
  -- groupOrbit r_crit = MulAction.orbit (TwoDiskCompoundSymmetryGroup r_crit)
  --                   = MulAction.orbit GG5_At_Critical_radius = GG5_orbit
  exact h_word_inf

/-- **Main Result**: The compound symmetry group GG5 is infinite. -/
theorem GG5_is_infinite : Infinite GG5_At_Critical_radius := by
  obtain ⟨z, hz⟩ := GG5_has_infinite_group_orbit
  exact GG5_infinite_of_infinite_orbit z hz

end TDCSG.CompoundSymmetry.GG5
