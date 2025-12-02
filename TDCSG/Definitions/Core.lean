/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Circle

/-!
# Core Definitions

This file contains the fundamental mathematical constants and algebraic structures
for the two-disk compound symmetry groups.

## Main definitions

- `Generator`: The four generators A, A⁻¹, B, B⁻¹ of the group
- `Word`: A word is a list of generators
- `φ`: The golden ratio $(1 + \sqrt{5})/2$
- `r_crit`: The critical radius $\sqrt{3 + φ}$ at which GG(5,5) becomes infinite
- `ζ₅`: The primitive 5th root of unity $e^{2πi/5}$
- `zeta5Circle`: ζ₅ as an element of the unit circle

## Notation

- `A⁻¹` for `Generator.Ainv`
- `B⁻¹` for `Generator.Binv`

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open Real

/-- The four generators A, A⁻¹, B, B⁻¹ of the two-disk compound symmetry group. -/
inductive Generator where
  | A | Ainv | B | Binv
  deriving DecidableEq, Repr

notation "A⁻¹" => Generator.Ainv
notation "B⁻¹" => Generator.Binv

/-- A word is a finite sequence of generators. -/
abbrev Word := List Generator

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def φ : ℝ := Real.goldenRatio

/-- The critical radius r_crit = √(3 + φ) at which GG(5,5) is infinite. -/
noncomputable def r_crit : ℝ := Real.sqrt (3 + φ)

open scoped Complex
open Complex

/-- The primitive 5th root of unity ζ₅ = e^(2πi/5). -/
noncomputable def ζ₅ : Complex := exp (2 * Real.pi * Complex.I / 5)

/-- ζ₅ is a primitive 5th root of unity. -/
lemma zeta5_isPrimitiveRoot : IsPrimitiveRoot ζ₅ 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

@[simp] lemma zeta5_abs : ‖ζ₅‖ = 1 :=
  IsPrimitiveRoot.norm'_eq_one zeta5_isPrimitiveRoot (by norm_num)

noncomputable def zeta5Circle : Circle :=
  ⟨ζ₅, mem_sphere_zero_iff_norm.2 zeta5_abs⟩

@[simp]
lemma zeta5Circle_coe : (zeta5Circle : ℂ) = ζ₅ := rfl

noncomputable def zeta5CirclePow (n : ℕ) : Circle := zeta5Circle ^ n

noncomputable def zeta5CircleInv : Circle := zeta5Circle⁻¹

@[simp]
lemma zeta5CircleInv_coe : (zeta5CircleInv : ℂ) = ζ₅⁻¹ := rfl

end TDCSG.Definitions
