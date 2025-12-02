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

- `genA_pow_five` : A^5 = id (generator A has order 5)
- `genB_pow_five` : B^5 = id (generator B has order 5)
- `genA_bijective_proof` : Proof that genA is bijective
- `genB_bijective_proof` : Proof that genB is bijective
- `orbit_eq_groupOrbit` : The word-based orbit equals the MulAction orbit
- `infinite_orbit_implies_infinite_group` : Infinite orbit implies infinite group

## N-fold Generalization

- `Circle_exp_pow_general` : Circle.exp theta ^ n = Circle.exp (n * theta)
- `Circle_exp_neg_two_pi_over_n_pow_n` : (Circle.exp (-2pi/n))^n = 1 for n >= 1
- `genA_n_pow_n` : (genA_n n)^n = id for n >= 1
- `genB_n_pow_n` : (genB_n n)^n = id for n >= 1
- `genA_n_bijective_proof` : genA_n is bijective for n >= 1
- `genB_n_bijective_proof` : genB_n is bijective for n >= 1

## Proof Strategy

1. Prove generators have order 5, hence are bijections
2. Show word-based orbit equals MulAction.orbit for the subgroup
3. Use contrapositive of `Finite.finite_mulAction_orbit`: infinite orbit implies infinite group
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions
open scoped Complex

/-! ### Circle Exponential Lemmas

The core circle exponential lemmas (Circle_exp_pow, circle_exp_neg_two_pi,
Circle_exp_neg_two_pi_over_n_pow_n) are defined in TDCSG.Definitions.GroupAction
and available via the `open TDCSG.Definitions` statement above.
-/

/-- 5 rotations by -2pi/5 = identity (key for order 5). -/
lemma Circle_exp_neg_two_pi_over_5_pow_5 : Circle.exp (-2 * Real.pi / 5) ^ 5 = 1 := by
  rw [Circle_exp_pow]
  have h : (5 : Nat) * (-2 * Real.pi / 5) = -2 * Real.pi := by ring
  rw [h]
  exact circle_exp_neg_two_pi

/-! ### Generator A Properties -/

/-- genA acts as identity outside the left disk. -/
lemma genA_outside (r : Real) (z : Complex) (hz : z ∉ leftDisk r) : genA r z = z := by
  unfold genA
  simp only [hz, if_false]

/-- genA acts as rotation inside the left disk. -/
lemma genA_inside (r : Real) (z : Complex) (hz : z ∈ leftDisk r) :
    genA r z = rotateAboutCircle leftCenter (Circle.exp (-2 * Real.pi / 5)) z := by
  unfold genA
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- Generator A has order 5: applying it 5 times gives the identity. -/
lemma genA_pow_five (r : Real) (z : Complex) :
    genA r (genA r (genA r (genA r (genA r z)))) = z := by
  by_cases hz : z ∈ leftDisk r
  . -- Inside case: 5 rotations = identity
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
          simp only [hrot, <- rotateAboutCircle_mul]
      _ = rotateAboutCircle leftCenter (a ^ 5) z := by
          congr 1; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = rotateAboutCircle leftCenter 1 z := by rw [ha, Circle_exp_neg_two_pi_over_5_pow_5]
      _ = z := rotateAboutCircle_one leftCenter z
  . -- Outside case: genA is identity
    simp only [genA_outside r z hz]

/-- Generator A is a bijection: it has order 5 (A^5 = id). -/
theorem genA_bijective_proof (r : Real) : Function.Bijective (genA r) := by
  constructor
  . -- Injective: if genA x = genA y, apply genA^4 to both sides
    intro x y hxy
    have hx : genA r (genA r (genA r (genA r (genA r x)))) = x := genA_pow_five r x
    have hy : genA r (genA r (genA r (genA r (genA r y)))) = y := genA_pow_five r y
    -- Apply genA r four times to both sides of hxy
    have h1 : genA r (genA r x) = genA r (genA r y) := congrArg (genA r) hxy
    have h2 : genA r (genA r (genA r x)) = genA r (genA r (genA r y)) := congrArg (genA r) h1
    have h3 : genA r (genA r (genA r (genA r x))) = genA r (genA r (genA r (genA r y))) := congrArg (genA r) h2
    have h4 : genA r (genA r (genA r (genA r (genA r x)))) = genA r (genA r (genA r (genA r (genA r y)))) := congrArg (genA r) h3
    rw [hx, hy] at h4
    exact h4
  . -- Surjective: preimage of y is genA^4 y
    intro y
    use genA r (genA r (genA r (genA r y)))
    exact genA_pow_five r y

/-! ### Generator B Properties -/

/-- genB acts as identity outside the right disk. -/
lemma genB_outside (r : Real) (z : Complex) (hz : z ∉ rightDisk r) : genB r z = z := by
  unfold genB
  simp only [hz, if_false]

/-- genB acts as rotation inside the right disk. -/
lemma genB_inside (r : Real) (z : Complex) (hz : z ∈ rightDisk r) :
    genB r z = rotateAboutCircle rightCenter (Circle.exp (-2 * Real.pi / 5)) z := by
  unfold genB
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- Generator B has order 5: applying it 5 times gives the identity. -/
lemma genB_pow_five (r : Real) (z : Complex) :
    genB r (genB r (genB r (genB r (genB r z)))) = z := by
  -- Case split on whether z is in the right disk
  by_cases hz : z ∈ rightDisk r
  . -- Inside disk: 5 rotations by -2pi/5 = rotation by -2pi = identity
    -- First show that genB preserves membership in rightDisk
    have h1 : genB r z ∈ rightDisk r := genB_preserves_rightDisk r z hz
    have h2 : genB r (genB r z) ∈ rightDisk r := genB_preserves_rightDisk r (genB r z) h1
    have h3 : genB r (genB r (genB r z)) ∈ rightDisk r :=
      genB_preserves_rightDisk r (genB r (genB r z)) h2
    have h4 : genB r (genB r (genB r (genB r z))) ∈ rightDisk r :=
      genB_preserves_rightDisk r (genB r (genB r (genB r z))) h3
    -- Define the rotation element
    set omega := Circle.exp (-2 * Real.pi / 5) with homega_def
    -- Rewrite the goal step by step, from outermost to innermost
    -- First, use the fact that genB on rightDisk = rotation
    calc genB r (genB r (genB r (genB r (genB r z))))
        = rotateAboutCircle rightCenter omega (genB r (genB r (genB r (genB r z)))) :=
          genB_in_disk_eq_rotateAboutCircle r _ h4
      _ = rotateAboutCircle rightCenter omega (rotateAboutCircle rightCenter omega (genB r (genB r (genB r z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r _ h3]
      _ = rotateAboutCircle rightCenter omega (rotateAboutCircle rightCenter omega
            (rotateAboutCircle rightCenter omega (genB r (genB r z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r _ h2]
      _ = rotateAboutCircle rightCenter omega (rotateAboutCircle rightCenter omega
            (rotateAboutCircle rightCenter omega (rotateAboutCircle rightCenter omega (genB r z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r _ h1]
      _ = rotateAboutCircle rightCenter omega (rotateAboutCircle rightCenter omega
            (rotateAboutCircle rightCenter omega (rotateAboutCircle rightCenter omega
              (rotateAboutCircle rightCenter omega z)))) := by
          rw [genB_in_disk_eq_rotateAboutCircle r z hz]
      _ = rotateAboutCircle rightCenter (omega ^ 5) z := by
          -- Use rotateAboutCircle_pow to collapse 5 nested rotations
          have h_iter : (rotateAboutCircle rightCenter omega)^[5] z =
              rotateAboutCircle rightCenter (omega ^ 5) z := rotateAboutCircle_pow rightCenter omega 5 z
          simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply] at h_iter
          exact h_iter
      _ = rotateAboutCircle rightCenter 1 z := by
          -- Show omega^5 = 1
          have omega_pow_five : omega ^ 5 = 1 := by
            rw [homega_def]
            ext
            rw [SubmonoidClass.coe_pow, Circle.coe_exp, Circle.coe_one]
            rw [<- Complex.exp_nat_mul]
            -- The goal is: cexp (5 * ((-2 * Real.pi / 5) * Complex.I)) = 1
            -- Need to show 5 * ((-2 * Real.pi / 5) * I) = -1 * (2pi * I)
            have h_eq : (5 : Nat) * (((-2 * Real.pi / 5 : Real) : Complex) * Complex.I) =
                (-1 : Int) * (2 * Real.pi * Complex.I) := by
              push_cast
              ring
            rw [h_eq, Complex.exp_int_mul_two_pi_mul_I]
          rw [omega_pow_five]
      _ = z := rotateAboutCircle_one rightCenter z
  . -- Outside disk: genB is the identity, so z stays z at each step
    have hgenB_id : forall w, w ∉ rightDisk r -> genB r w = w := fun w hw => by
      unfold genB
      simp only [hw, if_false]
    -- z not in rightDisk r, so genB r z = z
    rw [hgenB_id z hz]
    -- Now z not in rightDisk r implies genB r z = z, so we just have z
    rw [hgenB_id z hz, hgenB_id z hz, hgenB_id z hz, hgenB_id z hz]

/-- Generator B is a bijection: it has order 5 (B^5 = id). -/
theorem genB_bijective_proof (r : Real) : Function.Bijective (genB r) := by
  constructor
  . -- Injective: if genB x = genB y, apply genB^4 to both sides
    intro x y hxy
    have hx : genB r (genB r (genB r (genB r (genB r x)))) = x := genB_pow_five r x
    have hy : genB r (genB r (genB r (genB r (genB r y)))) = y := genB_pow_five r y
    -- Apply genB r four times to both sides of hxy
    have h1 : genB r (genB r x) = genB r (genB r y) := congrArg (genB r) hxy
    have h2 : genB r (genB r (genB r x)) = genB r (genB r (genB r y)) := congrArg (genB r) h1
    have h3 : genB r (genB r (genB r (genB r x))) = genB r (genB r (genB r (genB r y))) := congrArg (genB r) h2
    have h4 : genB r (genB r (genB r (genB r (genB r x)))) = genB r (genB r (genB r (genB r (genB r y)))) := congrArg (genB r) h3
    rw [hx, hy] at h4
    exact h4
  . -- Surjective: preimage of y is genB^4 y
    intro y
    use genB r (genB r (genB r (genB r y)))
    exact genB_pow_five r y

/-! ### Permutation Order Properties -/

/-- genA_perm has order 5 in the group Equiv.Perm Complex. -/
lemma genA_perm_pow_five (r : Real) : genA_perm r ^ 5 = 1 := by
  ext z
  simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
             Function.comp_apply, Equiv.Perm.coe_one, id_eq, genA_perm_apply]
  exact genA_pow_five r z

/-- genB_perm has order 5 in the group Equiv.Perm Complex. -/
lemma genB_perm_pow_five (r : Real) : genB_perm r ^ 5 = 1 := by
  ext z
  simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
             Function.comp_apply, Equiv.Perm.coe_one, id_eq, genB_perm_apply]
  exact genB_pow_five r z

/-! ### N-fold Generalized Properties

The core N-fold lemmas (genA_n_outside, genA_n_inside, genB_n_outside, genB_n_inside,
genA_n_pow_n, genB_n_pow_n, iterate_split, iterate_unsplit, and the iterate preservation
lemmas) are defined in TDCSG.Definitions.GroupAction and available via `open TDCSG.Definitions`.
-/

/-- Generalized generator A_n is a bijection for n >= 1. -/
theorem genA_n_bijective_proof (n : Nat) (hn : n >= 1) (r : Real) :
    Function.Bijective (genA_n n r) := by
  -- Key fact: genA_n^[n] = id
  have h_period : forall z, (genA_n n r)^[n] z = z := fun z => genA_n_pow_n n hn r z
  constructor
  . -- Injective
    intro x y hxy
    -- Apply f^[n-1] to both sides of hxy to get f^[n] x = f^[n] y, hence x = y
    have h_apply : forall k, (genA_n n r)^[k] (genA_n n r x) = (genA_n n r)^[k] (genA_n n r y) := by
      intro k
      induction k with
      | zero => simp [hxy]
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        exact congrArg (genA_n n r) ih
    have h_eq : (genA_n n r)^[n] x = (genA_n n r)^[n] y := by
      calc (genA_n n r)^[n] x
          = (genA_n n r)^[n - 1] (genA_n n r x) := iterate_split (genA_n n r) n hn x
        _ = (genA_n n r)^[n - 1] (genA_n n r y) := h_apply (n - 1)
        _ = (genA_n n r)^[n] y := (iterate_split (genA_n n r) n hn y).symm
    calc x = (genA_n n r)^[n] x := (h_period x).symm
      _ = (genA_n n r)^[n] y := h_eq
      _ = y := h_period y
  . -- Surjective
    intro y
    use (genA_n n r)^[n - 1] y
    calc genA_n n r ((genA_n n r)^[n - 1] y)
        = (genA_n n r)^[n] y := iterate_unsplit (genA_n n r) n hn y
      _ = y := h_period y

/-- Generalized generator B_n is a bijection for n >= 1. -/
theorem genB_n_bijective_proof (n : Nat) (hn : n >= 1) (r : Real) :
    Function.Bijective (genB_n n r) := by
  have h_period : forall z, (genB_n n r)^[n] z = z := fun z => genB_n_pow_n n hn r z
  constructor
  . -- Injective
    intro x y hxy
    have h_apply : forall k, (genB_n n r)^[k] (genB_n n r x) = (genB_n n r)^[k] (genB_n n r y) := by
      intro k
      induction k with
      | zero => simp [hxy]
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        exact congrArg (genB_n n r) ih
    have h_eq : (genB_n n r)^[n] x = (genB_n n r)^[n] y := by
      calc (genB_n n r)^[n] x
          = (genB_n n r)^[n - 1] (genB_n n r x) := iterate_split (genB_n n r) n hn x
        _ = (genB_n n r)^[n - 1] (genB_n n r y) := h_apply (n - 1)
        _ = (genB_n n r)^[n] y := (iterate_split (genB_n n r) n hn y).symm
    calc x = (genB_n n r)^[n] x := (h_period x).symm
      _ = (genB_n n r)^[n] y := h_eq
      _ = y := h_period y
  . -- Surjective
    intro y
    use (genB_n n r)^[n - 1] y
    calc genB_n n r ((genB_n n r)^[n - 1] y)
        = (genB_n n r)^[n] y := iterate_unsplit (genB_n n r) n hn y
      _ = y := h_period y

/-! ### Orbit Equivalence -/

/-- Convert a generator to the corresponding permutation in TwoDiskCompoundSymmetryGroup (5-fold). -/
private noncomputable def genToPerm (r : Real) : Generator -> TwoDiskCompoundSymmetryGroup 5 (by norm_num) r
  | .A => { val := genA_n_perm 5 (by norm_num) r, property := Subgroup.subset_closure (Set.mem_insert _ _) }
  | .Ainv => { val := (genA_n_perm 5 (by norm_num) r)⁻¹, property := Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) }
  | .B => { val := genB_n_perm 5 (by norm_num) r, property := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)) }
  | .Binv => { val := (genB_n_perm 5 (by norm_num) r)⁻¹, property := Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) }

/-- The action of genToPerm agrees with applyGen. -/
private lemma genToPerm_action (r : Real) (g : Generator) (p : Complex) :
    (genToPerm r g).val p = applyGen r p g := by
  cases g with
  | A =>
    simp only [genToPerm, applyGen, Subgroup.coe_mk, genA_n_perm, Equiv.ofBijective_apply]
    exact genA_eq_genA_n_5 r p
  | Ainv =>
    simp only [genToPerm, applyGen, Subgroup.coe_mk]
    have h : (genA_n_perm 5 (by norm_num) r)⁻¹ = (genA_n_perm 5 (by norm_num) r) ^ 4 := by
      have h5 : (genA_n_perm 5 (by norm_num) r) ^ 5 = 1 := by
        ext z
        simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
                   Function.comp_apply, Equiv.Perm.coe_one, id_eq]
        exact genA_n_pow_n 5 (by norm_num) r z
      calc (genA_n_perm 5 (by norm_num) r)⁻¹
          = (genA_n_perm 5 (by norm_num) r)⁻¹ * 1 := by simp
        _ = (genA_n_perm 5 (by norm_num) r)⁻¹ * (genA_n_perm 5 (by norm_num) r) ^ 5 := by rw [h5]
        _ = (genA_n_perm 5 (by norm_num) r) ^ 4 := by group
    conv_lhs => rw [h]
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
               Function.comp_apply, genA_n_perm, Equiv.ofBijective_apply]
    rw [genA_eq_genA_n_5, genA_eq_genA_n_5, genA_eq_genA_n_5, genA_eq_genA_n_5]
    rfl
  | B =>
    simp only [genToPerm, applyGen, Subgroup.coe_mk, genB_n_perm, Equiv.ofBijective_apply]
    exact genB_eq_genB_n_5 r p
  | Binv =>
    simp only [genToPerm, applyGen, Subgroup.coe_mk]
    have h : (genB_n_perm 5 (by norm_num) r)⁻¹ = (genB_n_perm 5 (by norm_num) r) ^ 4 := by
      have h5 : (genB_n_perm 5 (by norm_num) r) ^ 5 = 1 := by
        ext z
        simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
                   Function.comp_apply, Equiv.Perm.coe_one, id_eq]
        exact genB_n_pow_n 5 (by norm_num) r z
      calc (genB_n_perm 5 (by norm_num) r)⁻¹
          = (genB_n_perm 5 (by norm_num) r)⁻¹ * 1 := by simp
        _ = (genB_n_perm 5 (by norm_num) r)⁻¹ * (genB_n_perm 5 (by norm_num) r) ^ 5 := by rw [h5]
        _ = (genB_n_perm 5 (by norm_num) r) ^ 4 := by group
    conv_lhs => rw [h]
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
               Function.comp_apply, genB_n_perm, Equiv.ofBijective_apply]
    rw [genB_eq_genB_n_5, genB_eq_genB_n_5, genB_eq_genB_n_5, genB_eq_genB_n_5]
    rfl

/-- Convert a word to a group element (product of generators from right to left).
    For word [g1, g2, g3], this produces genToPerm g3 * genToPerm g2 * genToPerm g1. -/
private noncomputable def wordToPerm (r : Real) : Word -> TwoDiskCompoundSymmetryGroup 5 (by norm_num) r
  | [] => 1
  | g :: gs => wordToPerm r gs * genToPerm r g

/-- Key lemma: wordToPerm applied to z equals applyWord. -/
private lemma wordToPerm_action (r : Real) (w : Word) (p : Complex) :
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

/-- Every element reachable by a word is in the MulAction orbit of the subgroup (5-fold). -/
lemma word_orbit_subset_group_orbit (r : Real) (z : Complex) :
    orbit r z ⊆ groupOrbit 5 (by norm_num) r z := by
  intro w hw
  obtain ⟨word, hw_eq⟩ := hw
  unfold groupOrbit
  rw [MulAction.mem_orbit_iff]
  use wordToPerm r word
  rw [<- hw_eq]
  exact wordToPerm_action r word z

/-- Helper lemma: wordToPerm distributes over append in reverse order. -/
private lemma wordToPerm_append (r : Real) (u v : Word) :
    wordToPerm r (u ++ v) = wordToPerm r v * wordToPerm r u := by
  induction u with
  | nil => simp [wordToPerm]
  | cons g gs ih =>
    simp only [List.cons_append, wordToPerm]
    rw [ih]
    group

/-- Helper: every element of the closure has a corresponding word.
    For any g in TwoDiskCompoundSymmetryGroup 5 r, there exists a word w
    such that g.val = (wordToPerm r w).val as permutations. -/
private lemma closure_element_has_word (r : Real) (g : TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) :
    exists w : Word, g.val = (wordToPerm r w).val := by
  obtain ⟨g_perm, hg⟩ := g
  -- Use closure induction with predicate: exists w, g_perm = (wordToPerm r w).val
  refine Subgroup.closure_induction (p := fun g _ => exists w : Word, g = (wordToPerm r w).val)
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
    -- If g corresponds to w1 and h corresponds to w2, then g * h corresponds to w2 ++ w1
    intro g' h' _ _ ⟨w1, hw1⟩ ⟨w2, hw2⟩
    use w2 ++ w1
    rw [hw1, hw2, wordToPerm_append]
    simp only [Subgroup.coe_mul]
  case inv =>
    -- If g corresponds to w, then g^-1 corresponds to reversed word with inverted generators
    intro g' _ ⟨w, hw⟩
    -- Define the inverse of a generator
    let invGen : Generator -> Generator
      | .A => .Ainv
      | .Ainv => .A
      | .B => .Binv
      | .Binv => .B
    use (w.reverse.map invGen)
    rw [hw]
    -- Need: ((wordToPerm r w).val)^-1 = (wordToPerm r (w.reverse.map invGen)).val
    -- First show that invGen inverts generators at the permutation level
    have h_invGen : forall gen, (genToPerm r (invGen gen)).val = ((genToPerm r gen).val)⁻¹ := by
      intro gen
      cases gen <;> simp only [invGen, genToPerm, Subgroup.coe_mk, inv_inv]
    -- Prove the general lemma about word inversion
    have h_rev_inv : forall (v : Word),
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
    rw [<- h_rev_inv w]

/-- Every element in the MulAction orbit is reachable by some word (5-fold). -/
lemma group_orbit_subset_word_orbit (r : Real) (z : Complex) :
    groupOrbit 5 (by norm_num) r z ⊆ orbit r z := by
  intro w hw
  unfold groupOrbit at hw
  rw [MulAction.mem_orbit_iff] at hw
  obtain ⟨g, hgw⟩ := hw
  -- g is in TwoDiskCompoundSymmetryGroup 5 r, so there exists word w such that g = wordToPerm r w
  obtain ⟨word, hword⟩ := closure_element_has_word r g
  -- w = g * z = g.val z = (wordToPerm r word).val z = applyWord r word z
  use word
  rw [<- hgw]
  -- Goal: applyWord r word z = g * z
  -- g * z = g.val z for subgroup elements acting on the type
  -- g.val = (wordToPerm r word).val by hword
  -- (wordToPerm r word).val z = applyWord r word z by wordToPerm_action
  have h2 : (wordToPerm r word).val z = applyWord r word z := wordToPerm_action r word z
  calc applyWord r word z
      = (wordToPerm r word).val z := h2.symm
    _ = g.val z := by rw [<- hword]
    _ = g • z := rfl

/-- The word-based orbit equals the group-theoretic MulAction orbit (5-fold).

    This is the key bridge between the existing proof infrastructure
    (which uses words) and the proper group-theoretic formulation. -/
theorem orbit_eq_groupOrbit (r : Real) (z : Complex) :
    orbit r z = groupOrbit 5 (by norm_num) r z := by
  apply Set.eq_of_subset_of_subset
  . exact word_orbit_subset_group_orbit r z
  . exact group_orbit_subset_word_orbit r z

/-! ### Infinite Orbit Implies Infinite Group -/

/-- If the word-based orbit is infinite, the group orbit is infinite (5-fold). -/
lemma word_orbit_infinite_iff_group_orbit_infinite (r : Real) (z : Complex) :
    (orbit r z).Infinite <-> (groupOrbit 5 (by norm_num) r z).Infinite := by
  rw [orbit_eq_groupOrbit]

/-- Key lemma: If a group action has an infinite orbit, the group is infinite.

    This is the contrapositive of Mathlib's `Finite.finite_mulAction_orbit`:
    if the group were finite, all orbits would be finite. -/
lemma infinite_orbit_implies_infinite_group {G : Type*} [Group G] [MulAction G Complex]
    (z : Complex) (h : (MulAction.orbit G z).Infinite) : Infinite G := by
  by_contra hfin
  push_neg at hfin
  haveI : Finite G := hfin
  exact h (Finite.finite_mulAction_orbit z)

/-- The compound symmetry group is infinite if it has a point with infinite orbit (5-fold). -/
theorem CompoundSymmetryGroup_infinite_of_infinite_orbit (r : Real) (z : Complex)
    (h : (groupOrbit 5 (by norm_num) r z).Infinite) : Infinite (TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) := by
  exact infinite_orbit_implies_infinite_group z h

/-- GG5 is infinite if it has a point with infinite orbit. -/
theorem GG5_infinite_of_infinite_orbit (z : Complex)
    (h : (GG5_orbit z).Infinite) : Infinite GG5_At_Critical_radius := by
  exact CompoundSymmetryGroup_infinite_of_infinite_orbit r_crit z h

/-! ### Bridge to Existing Infrastructure -/

/-- The existing proof gives us a point with infinite word-orbit.
    This lifts to infinite group orbit. -/
theorem GG5_has_infinite_group_orbit :
    exists z : Complex, (GG5_orbit z).Infinite := by
  obtain ⟨x0, hx0_mem, hx0_inf⟩ := GG5_IET_has_infinite_orbit
  use segmentPoint x0
  -- GG5_orbit = MulAction.orbit GG5
  -- Need to show this equals the word-based orbit
  show (MulAction.orbit GG5_At_Critical_radius (segmentPoint x0)).Infinite
  -- From IETOrbit.lean: IET infinite orbit implies word-based orbit is infinite
  have h_word_inf : (orbit r_crit (segmentPoint x0)).Infinite :=
    IET_orbit_infinite_implies_group_orbit_infinite x0 hx0_mem hx0_inf
  -- From orbit_eq_groupOrbit: word-based orbit = group orbit (MulAction.orbit)
  rw [orbit_eq_groupOrbit] at h_word_inf
  -- groupOrbit _root_.r_crit = MulAction.orbit (TwoDiskCompoundSymmetryGroup _root_.r_crit)
  --                   = MulAction.orbit GG5_At_Critical_radius = GG5_orbit
  exact h_word_inf

/-- **Main Result**: The compound symmetry group GG5 is infinite. -/
theorem GG5_is_infinite : Infinite GG5_At_Critical_radius := by
  obtain ⟨z, hz⟩ := GG5_has_infinite_group_orbit
  exact GG5_infinite_of_infinite_orbit z hz

end TDCSG.CompoundSymmetry.GG5
