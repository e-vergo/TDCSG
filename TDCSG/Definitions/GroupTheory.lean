/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.MainTheorem
import TDCSG.Definitions.GroupAction
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Compound Symmetry Group - Proofs and Extensions

This file provides the proofs of the axioms stated in MainTheorem.lean, plus additional
supporting infrastructure for working with the compound symmetry groups.

## Structure

- **MainTheorem.lean**: Contains the core definitions (genA_n, genB_n, TwoDiskCompoundSymmetryGroup, etc.)
- **This file**: Provides proofs that the generators are bijective, plus specialized 5-fold infrastructure

## Main Results

- `genA_n_bijective`: Proof that genA_n is bijective for n ≥ 1
- `genB_n_bijective`: Proof that genB_n is bijective for n ≥ 1
- Specialized 5-fold infrastructure (genA_perm, genB_perm, etc.)
- Connection lemmas between 5-fold and N-fold versions

## Design Notes

The main definitions live in MainTheorem.lean so that file is self-contained and readable.
This file contains the technical proofs using Circle exponential periodicity and
disk-preserving rotation properties.
-/

namespace TDCSG.Definitions

open scoped Complex

/-! ### Import Main Definitions -/

-- Main definitions come from MainTheorem
open _root_ (φ r_crit genA_n genB_n genA_n_perm genB_n_perm TwoDiskCompoundSymmetryGroup GG5_At_Critical_radius)

/-- Original generator A is the 5-fold specialization. -/
lemma genA_eq_genA_n_5 (r : Real) (z : Complex) : genA r z = genA_n 5 r z := by
  unfold genA genA_n
  simp only [Nat.cast_ofNat]

/-- Original generator B is the 5-fold specialization. -/
lemma genB_eq_genB_n_5 (r : Real) (z : Complex) : genB r z = genB_n 5 r z := by
  unfold genB genB_n
  simp only [Nat.cast_ofNat]

/-! ### Helper Lemmas for Circle Exponential -/

/-- Circle.exp theta ^ n = Circle.exp (n * theta). -/
private lemma Circle_exp_pow (theta : Real) (n : Nat) : Circle.exp theta ^ n = Circle.exp (n * theta) := by
  induction n with
  | zero => simp [Circle.exp_zero]
  | succ n ih =>
    rw [pow_succ, ih, <- Circle.exp_add]
    congr 1
    push_cast
    ring

/-- Circle.exp (-2pi) = 1, the fundamental periodicity. -/
private lemma circle_exp_neg_two_pi : Circle.exp (-2 * Real.pi) = 1 := by
  apply Subtype.ext
  simp only [Circle.coe_exp, Circle.coe_one]
  push_cast
  have h : (-2 : Complex) * Real.pi * Complex.I = -(2 * Real.pi * Complex.I) := by ring
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- 5 rotations by -2pi/5 = identity (key for order 5). -/
private lemma Circle_exp_neg_two_pi_over_5_pow_5 : Circle.exp (-2 * Real.pi / 5) ^ 5 = 1 := by
  rw [Circle_exp_pow]
  have h : (5 : Nat) * (-2 * Real.pi / 5) = -2 * Real.pi := by ring
  rw [h]
  exact circle_exp_neg_two_pi

/-- n rotations by -2pi/n = identity for n >= 1 (general order-n property). -/
private lemma Circle_exp_neg_two_pi_over_n_pow_n (n : Nat) (hn : n >= 1) :
    Circle.exp (-2 * Real.pi / n) ^ n = 1 := by
  rw [Circle_exp_pow]
  have h : (n : Real) * (-2 * Real.pi / n) = -2 * Real.pi := by field_simp
  rw [h]
  exact circle_exp_neg_two_pi

/-! ### Generator A Helper Lemmas -/

/-- genA acts as identity outside the left disk. -/
private lemma genA_outside (r : Real) (z : Complex) (hz : z ∉ leftDisk r) : genA r z = z := by
  unfold genA
  simp only [hz, if_false]

/-- genA acts as rotation inside the left disk. -/
private lemma genA_inside (r : Real) (z : Complex) (hz : z ∈ leftDisk r) :
    genA r z = rotateAboutCircle leftCenter (Circle.exp (-2 * Real.pi / 5)) z := by
  unfold genA
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- Rotation about leftCenter preserves leftDisk membership. -/
private lemma rotateAboutCircle_leftCenter_preserves_leftDisk (a : Circle) (r : Real) (z : Complex)
    (hz : z ∈ leftDisk r) : rotateAboutCircle leftCenter a z ∈ leftDisk r := by
  unfold leftDisk
  have h_center : leftCenter = (-1 : Complex) := by unfold leftCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk (-1) a r z hz

/-- Generator A has order 5: applying it 5 times gives the identity. -/
private lemma genA_pow_five (r : Real) (z : Complex) :
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

/-! ### Generator B Helper Lemmas -/

/-- genB acts as identity outside the right disk. -/
private lemma genB_outside (r : Real) (z : Complex) (hz : z ∉ rightDisk r) : genB r z = z := by
  unfold genB
  simp only [hz, if_false]

/-- genB acts as rotation inside the right disk. -/
private lemma genB_inside (r : Real) (z : Complex) (hz : z ∈ rightDisk r) :
    genB r z = rotateAboutCircle rightCenter (Circle.exp (-2 * Real.pi / 5)) z := by
  unfold genB
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- Rotation about rightCenter preserves rightDisk membership. -/
private lemma rotateAboutCircle_rightCenter_preserves_rightDisk (a : Circle) (r : Real) (z : Complex)
    (hz : z ∈ rightDisk r) : rotateAboutCircle rightCenter a z ∈ rightDisk r := by
  unfold rightDisk
  have h_center : rightCenter = (1 : Complex) := by unfold rightCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk 1 a r z hz

/-- Generator B has order 5: applying it 5 times gives the identity. -/
private lemma genB_pow_five (r : Real) (z : Complex) :
    genB r (genB r (genB r (genB r (genB r z)))) = z := by
  by_cases hz : z ∈ rightDisk r
  . -- Inside case: 5 rotations = identity
    set a := Circle.exp (-2 * Real.pi / 5) with ha
    set rot := rotateAboutCircle rightCenter a with hrot
    -- Each genB application preserves disk membership and equals rotation
    have step1 : genB r z = rot z := genB_inside r z hz
    have mem1 : rot z ∈ rightDisk r := rotateAboutCircle_rightCenter_preserves_rightDisk a r z hz
    have step2 : genB r (rot z) = rot (rot z) := genB_inside r (rot z) mem1
    have mem2 : rot (rot z) ∈ rightDisk r := rotateAboutCircle_rightCenter_preserves_rightDisk a r _ mem1
    have step3 : genB r (rot (rot z)) = rot (rot (rot z)) := genB_inside r _ mem2
    have mem3 : rot (rot (rot z)) ∈ rightDisk r := rotateAboutCircle_rightCenter_preserves_rightDisk a r _ mem2
    have step4 : genB r (rot (rot (rot z))) = rot (rot (rot (rot z))) := genB_inside r _ mem3
    have mem4 : rot (rot (rot (rot z))) ∈ rightDisk r := rotateAboutCircle_rightCenter_preserves_rightDisk a r _ mem3
    have step5 : genB r (rot (rot (rot (rot z)))) = rot (rot (rot (rot (rot z)))) := genB_inside r _ mem4
    -- Chain together: 5 genB applications = 5 rotations = rotation by power 5
    calc genB r (genB r (genB r (genB r (genB r z))))
        = genB r (genB r (genB r (genB r (rot z)))) := by rw [step1]
      _ = genB r (genB r (genB r (rot (rot z)))) := by rw [step2]
      _ = genB r (genB r (rot (rot (rot z)))) := by rw [step3]
      _ = genB r (rot (rot (rot (rot z)))) := by rw [step4]
      _ = rot (rot (rot (rot (rot z)))) := by rw [step5]
      _ = rotateAboutCircle rightCenter (a * (a * (a * (a * a)))) z := by
          simp only [hrot, <- rotateAboutCircle_mul]
      _ = rotateAboutCircle rightCenter (a ^ 5) z := by
          congr 1; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = rotateAboutCircle rightCenter 1 z := by rw [ha, Circle_exp_neg_two_pi_over_5_pow_5]
      _ = z := rotateAboutCircle_one rightCenter z
  . -- Outside case: genB is identity
    simp only [genB_outside r z hz]

/-! ### Generators as Permutations -/

/-- Generator A is a bijection: it has order 5 (A^5 = id). -/
lemma genA_bijective (r : Real) : Function.Bijective (genA r) := by
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

/-- Generator B is a bijection: it has order 5 (B^5 = id). -/
lemma genB_bijective (r : Real) : Function.Bijective (genB r) := by
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

/-- Generator A as an element of `Equiv.Perm C`. -/
noncomputable def genA_perm (r : Real) : Equiv.Perm Complex :=
  Equiv.ofBijective (genA r) (genA_bijective r)

/-- Generator B as an element of `Equiv.Perm C`. -/
noncomputable def genB_perm (r : Real) : Equiv.Perm Complex :=
  Equiv.ofBijective (genB r) (genB_bijective r)

/-- The action of genA_perm agrees with genA. -/
@[simp]
lemma genA_perm_apply (r : Real) (z : Complex) : genA_perm r z = genA r z := rfl

/-- The action of genB_perm agrees with genB. -/
@[simp]
lemma genB_perm_apply (r : Real) (z : Complex) : genB_perm r z = genB r z := rfl

/-! ### N-fold Generalized Permutations -/

/-- genA_n acts as identity outside the left disk. -/
private lemma genA_n_outside (n : Nat) (r : Real) (z : Complex) (hz : z ∉ leftDisk r) :
    genA_n n r z = z := by
  unfold genA_n
  simp only [hz, if_false]

/-- genA_n acts as rotation inside the left disk. -/
private lemma genA_n_inside (n : Nat) (r : Real) (z : Complex) (hz : z ∈ leftDisk r) :
    genA_n n r z = rotateAboutCircle leftCenter (Circle.exp (-2 * Real.pi / n)) z := by
  unfold genA_n
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- genB_n acts as identity outside the right disk. -/
private lemma genB_n_outside (n : Nat) (r : Real) (z : Complex) (hz : z ∉ rightDisk r) :
    genB_n n r z = z := by
  unfold genB_n
  simp only [hz, if_false]

/-- genB_n acts as rotation inside the right disk. -/
private lemma genB_n_inside (n : Nat) (r : Real) (z : Complex) (hz : z ∈ rightDisk r) :
    genB_n n r z = rotateAboutCircle rightCenter (Circle.exp (-2 * Real.pi / n)) z := by
  unfold genB_n
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

/-- Helper: rotation about leftCenter preserves leftDisk through iterations. -/
private lemma rotateAboutCircle_leftCenter_iterate_preserves_leftDisk' (a : Circle) (r : Real) (k : Nat)
    (w : Complex) (hw : w ∈ leftDisk r) :
    (rotateAboutCircle leftCenter a)^[k] w ∈ leftDisk r := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact rotateAboutCircle_leftCenter_preserves_leftDisk a r _ ih

/-- Helper: rotation about rightCenter preserves rightDisk through iterations. -/
private lemma rotateAboutCircle_rightCenter_iterate_preserves_rightDisk' (a : Circle) (r : Real) (k : Nat)
    (w : Complex) (hw : w ∈ rightDisk r) :
    (rotateAboutCircle rightCenter a)^[k] w ∈ rightDisk r := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact rotateAboutCircle_rightCenter_preserves_rightDisk a r _ ih

/-- Generator A_n has order n: applying it n times gives the identity. -/
private lemma genA_n_pow_n (n : Nat) (hn : n >= 1) (r : Real) (z : Complex) :
    (genA_n n r)^[n] z = z := by
  by_cases hz : z ∈ leftDisk r
  . -- Inside case: n rotations = identity
    set a := Circle.exp (-2 * Real.pi / n) with ha
    -- Show that iterating genA_n n times equals iterating rotation n times
    have h_eq_rot : forall k : Nat, forall w : Complex, w ∈ leftDisk r ->
        (genA_n n r)^[k] w = (rotateAboutCircle leftCenter a)^[k] w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro w hw
        simp only [Function.iterate_succ', Function.comp_apply]
        have hw' : (rotateAboutCircle leftCenter a)^[k] w ∈ leftDisk r :=
          rotateAboutCircle_leftCenter_iterate_preserves_leftDisk' a r k w hw
        rw [ih w hw]
        rw [genA_n_inside n r _ hw']
    rw [h_eq_rot n z hz]
    -- Now use rotateAboutCircle_pow and periodicity
    rw [rotateAboutCircle_pow]
    rw [ha, Circle_exp_neg_two_pi_over_n_pow_n n hn]
    exact rotateAboutCircle_one leftCenter z
  . -- Outside case: genA_n is identity
    have h_id : forall k : Nat, (genA_n n r)^[k] z = z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ih]
        exact genA_n_outside n r z hz
    exact h_id n

/-- Generator B_n has order n: applying it n times gives the identity. -/
private lemma genB_n_pow_n (n : Nat) (hn : n >= 1) (r : Real) (z : Complex) :
    (genB_n n r)^[n] z = z := by
  by_cases hz : z ∈ rightDisk r
  . -- Inside case: n rotations = identity
    set a := Circle.exp (-2 * Real.pi / n) with ha
    -- Show that iterating genB_n n times equals iterating rotation n times
    have h_eq_rot : forall k : Nat, forall w : Complex, w ∈ rightDisk r ->
        (genB_n n r)^[k] w = (rotateAboutCircle rightCenter a)^[k] w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro w hw
        simp only [Function.iterate_succ', Function.comp_apply]
        have hw' : (rotateAboutCircle rightCenter a)^[k] w ∈ rightDisk r :=
          rotateAboutCircle_rightCenter_iterate_preserves_rightDisk' a r k w hw
        rw [ih w hw]
        rw [genB_n_inside n r _ hw']
    rw [h_eq_rot n z hz]
    -- Now use rotateAboutCircle_pow and periodicity
    rw [rotateAboutCircle_pow]
    rw [ha, Circle_exp_neg_two_pi_over_n_pow_n n hn]
    exact rotateAboutCircle_one rightCenter z
  . -- Outside case: genB_n is identity
    have h_id : forall k : Nat, (genB_n n r)^[k] z = z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ih]
        exact genB_n_outside n r z hz
    exact h_id n

/-- Helper: f^[n] x = f^[n-1] (f x) when n >= 1. -/
private lemma iterate_split (f : Complex -> Complex) (n : Nat) (hn : n >= 1) (x : Complex) :
    f^[n] x = f^[n - 1] (f x) := by
  have h : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  conv_lhs => rw [h]
  rw [Function.iterate_succ_apply']
  exact (Function.Commute.iterate_self f (n - 1) x).symm

/-- Helper: f (f^[n-1] x) = f^[n] x when n >= 1. -/
private lemma iterate_unsplit (f : Complex -> Complex) (n : Nat) (hn : n >= 1) (x : Complex) :
    f (f^[n - 1] x) = f^[n] x := by
  have h : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  conv_rhs => rw [h]
  exact (Function.iterate_succ_apply' f (n - 1) x).symm

/-- Generalized bijection lemma for genA_n.
    For n >= 1, genA_n n r is a bijection of order n. -/
lemma genA_n_bijective (n : Nat) (hn : n >= 1) (r : Real) : Function.Bijective (genA_n n r) := by
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

/-- Generalized bijection lemma for genB_n.
    For n >= 1, genB_n n r is a bijection of order n. -/
lemma genB_n_bijective (n : Nat) (hn : n >= 1) (r : Real) : Function.Bijective (genB_n n r) := by
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

/-! ### Group Action and Orbits -/

/-- The MulAction orbit of a point under the compound symmetry group GG(n,n).

    This uses Mathlib's standard `MulAction.orbit` which gives the set
    `{g * z | g in G}` for a group G acting on a type. -/
noncomputable def groupOrbit (n : Nat) (hn : n >= 1) (r : Real) (z : Complex) : Set Complex :=
  MulAction.orbit (TwoDiskCompoundSymmetryGroup n hn r) z

/-- The GG5 orbit of a point (5-fold specialization). -/
noncomputable def GG5_orbit (z : Complex) : Set Complex :=
  MulAction.orbit GG5_At_Critical_radius z

/-! ### Specialization Lemmas for 5-fold Case -/

/-- The 5-fold generators are equal when viewed as permutations. -/
private lemma genA_n_perm_5_eq_genA_perm (r : Real) :
    (genA_n_perm 5 (by norm_num) r : Equiv.Perm Complex) = genA_perm r := by
  ext z
  exact genA_eq_genA_n_5 r z

/-- The 5-fold generators are equal when viewed as permutations. -/
private lemma genB_n_perm_5_eq_genB_perm (r : Real) :
    (genB_n_perm 5 (by norm_num) r : Equiv.Perm Complex) = genB_perm r := by
  ext z
  exact genB_eq_genB_n_5 r z

/-- The 5-fold compound symmetry group equals the closure of the original generators.
    This lemma establishes backward compatibility with existing proofs. -/
lemma TwoDiskCompoundSymmetryGroup_5_eq (r : Real) :
    TwoDiskCompoundSymmetryGroup 5 (by norm_num) r =
    Subgroup.closure {genA_perm r, genB_perm r} := by
  unfold TwoDiskCompoundSymmetryGroup
  simp only [genA_n_perm_5_eq_genA_perm, genB_n_perm_5_eq_genB_perm]

/-- The 5-fold group orbit equals the orbit under the original generators. -/
lemma groupOrbit_5_eq (r : Real) (z : Complex) :
    groupOrbit 5 (by norm_num) r z =
    MulAction.orbit (Subgroup.closure {genA_perm r, genB_perm r}) z := by
  unfold groupOrbit
  rw [TwoDiskCompoundSymmetryGroup_5_eq]

end TDCSG.Definitions
