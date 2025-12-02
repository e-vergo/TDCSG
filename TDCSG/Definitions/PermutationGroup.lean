/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.GroupAction
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Permutation Group Embeddings

This file defines the embedding of generators and words into the permutation group structure,
establishing the correspondence between syntactic word operations and semantic group actions.

## Main definitions

- `genToPerm`: Maps a generator to its corresponding group element
- `wordToPerm`: Maps a word (list of generators) to its corresponding group element

## Main results

- `genToPerm_action`: Acting with genToPerm equals applying the generator
- `wordToPerm_action`: Acting with wordToPerm equals applying the word
- `wordToPerm_append`: Word concatenation corresponds to group multiplication
- `closure_element_has_word`: Every group element has a word representation

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open scoped Complex

lemma genA_eq_genA_n_5 (r : Real) (z : Complex) : genA r z = genA_n 5 r z := by
  unfold genA genA_n
  simp only [Nat.cast_ofNat]

lemma genB_eq_genB_n_5 (r : Real) (z : Complex) : genB r z = genB_n 5 r z := by
  unfold genB genB_n
  simp only [Nat.cast_ofNat]

/-- Convert a single generator to its corresponding group element -/
noncomputable def genToPerm (r : Real) : Generator -> TwoDiskCompoundSymmetryGroup 5 (by norm_num) r
  | .A => { val := genA_n_perm 5 (by norm_num) r, property := Subgroup.subset_closure (Set.mem_insert _ _) }
  | .Ainv => { val := (genA_n_perm 5 (by norm_num) r)⁻¹, property := Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) }
  | .B => { val := genB_n_perm 5 (by norm_num) r, property := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)) }
  | .Binv => { val := (genB_n_perm 5 (by norm_num) r)⁻¹, property := Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) }

lemma genToPerm_action (r : Real) (g : Generator) (p : Complex) :
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

/-- Convert a word (list of generators) to its corresponding group element -/
noncomputable def wordToPerm (r : Real) : Word -> TwoDiskCompoundSymmetryGroup 5 (by norm_num) r
  | [] => 1
  | g :: gs => wordToPerm r gs * genToPerm r g

lemma wordToPerm_action (r : Real) (w : Word) (p : Complex) :
    (wordToPerm r w).val p = applyWord r w p := by
  induction w generalizing p with
  | nil =>
    simp only [wordToPerm, applyWord, List.foldl_nil]
    rfl
  | cons g gs ih =>
    simp only [wordToPerm, applyWord, List.foldl_cons]

    have h1 : (wordToPerm r gs * genToPerm r g).val p =
              (wordToPerm r gs).val ((genToPerm r g).val p) := by
      simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h1, genToPerm_action, ih]
    rfl

lemma wordToPerm_append (r : Real) (u v : Word) :
    wordToPerm r (u ++ v) = wordToPerm r v * wordToPerm r u := by
  induction u with
  | nil => simp [wordToPerm]
  | cons g gs ih =>
    simp only [List.cons_append, wordToPerm]
    rw [ih]
    group

lemma closure_element_has_word (r : Real) (g : TwoDiskCompoundSymmetryGroup 5 (by norm_num) r) :
    exists w : Word, g.val = (wordToPerm r w).val := by
  obtain ⟨g_perm, hg⟩ := g

  refine Subgroup.closure_induction (p := fun g _ => exists w : Word, g = (wordToPerm r w).val)
    ?mem ?one ?mul ?inv hg
  case mem =>

    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    cases hx with
    | inl h =>

      use [Generator.A]
      rw [h]
      simp only [wordToPerm, genToPerm, one_mul, Subgroup.coe_mk]
    | inr h =>

      use [Generator.B]
      rw [h]
      simp only [wordToPerm, genToPerm, one_mul, Subgroup.coe_mk]
  case one =>

    use []
    simp only [wordToPerm, Subgroup.coe_one]
  case mul =>

    intro g' h' _ _ ⟨w1, hw1⟩ ⟨w2, hw2⟩
    use w2 ++ w1
    rw [hw1, hw2, wordToPerm_append]
    simp only [Subgroup.coe_mul]
  case inv =>

    intro g' _ ⟨w, hw⟩

    let invGen : Generator -> Generator
      | .A => .Ainv
      | .Ainv => .A
      | .B => .Binv
      | .Binv => .B
    use (w.reverse.map invGen)
    rw [hw]

    have h_invGen : forall gen, (genToPerm r (invGen gen)).val = ((genToPerm r gen).val)⁻¹ := by
      intro gen
      cases gen <;> simp only [invGen, genToPerm, Subgroup.coe_mk, inv_inv]

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

end TDCSG.Definitions
