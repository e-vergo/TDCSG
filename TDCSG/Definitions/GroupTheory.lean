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

-- Main definitions and bijectivity proofs come from MainTheorem
open _root_ (φ r_crit genA_n genB_n genA_n_bijective genB_n_bijective genA_n_perm genB_n_perm TwoDiskCompoundSymmetryGroup GG5_At_Critical_radius)

/-! ### 5-fold Specialization

This section provides the 5-fold specialization of the N-fold generators,
maintaining backward compatibility with existing proofs that use genA and genB
instead of genA_n 5 and genB_n 5.
-/

/-- Original generator A is the 5-fold specialization of genA_n. -/
lemma genA_eq_genA_n_5 (r : Real) (z : Complex) : genA r z = genA_n 5 r z := by
  unfold genA genA_n
  simp only [Nat.cast_ofNat]

/-- Original generator B is the 5-fold specialization of genB_n. -/
lemma genB_eq_genB_n_5 (r : Real) (z : Complex) : genB r z = genB_n 5 r z := by
  unfold genB genB_n
  simp only [Nat.cast_ofNat]

/-! ### 5-fold Bijectivity

The 5-fold generators inherit bijectivity from the N-fold general case.
-/

/-- Generator A is bijective (5-fold specialization of N-fold bijectivity). -/
lemma genA_bijective (r : Real) : Function.Bijective (genA r) := by
  have h : genA r = genA_n 5 r := funext (genA_eq_genA_n_5 r)
  rw [h]
  exact genA_n_bijective 5 (by norm_num) r

/-- Generator B is bijective (5-fold specialization of N-fold bijectivity). -/
lemma genB_bijective (r : Real) : Function.Bijective (genB r) := by
  have h : genB r = genB_n 5 r := funext (genB_eq_genB_n_5 r)
  rw [h]
  exact genB_n_bijective 5 (by norm_num) r

/-! ### 5-fold Permutation Lifts -/

/-- Generator A as an element of `Equiv.Perm ℂ`. -/
noncomputable def genA_perm (r : Real) : Equiv.Perm Complex :=
  Equiv.ofBijective (genA r) (genA_bijective r)

/-- Generator B as an element of `Equiv.Perm ℂ`. -/
noncomputable def genB_perm (r : Real) : Equiv.Perm Complex :=
  Equiv.ofBijective (genB r) (genB_bijective r)

/-- The action of genA_perm agrees with genA. -/
@[simp]
lemma genA_perm_apply (r : Real) (z : Complex) : genA_perm r z = genA r z := rfl

/-- The action of genB_perm agrees with genB. -/
@[simp]
lemma genB_perm_apply (r : Real) (z : Complex) : genB_perm r z = genB r z := rfl

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
