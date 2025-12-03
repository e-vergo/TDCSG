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

- `Generator`: The four generators A, A⁻¹, B, B⁻¹ of the group (with Inv instance)
- `Word`: A word is a list of generators
- `φ`: The golden ratio (1 + √5)/2
- `r_crit`: The critical radius √(3 + φ) at which GG(5,5) becomes infinite
- `ζ₅`: The primitive 5th root of unity e^(2πi/5)
- `zeta5Circle`: ζ₅ as an element of the unit circle

## Algebraic Structure

The `Generator` type has an `Inv` instance, allowing the use of `g⁻¹` notation.
The inverse is defined algebraically: A⁻¹ inverts A, B⁻¹ inverts B, and the
operation is involutive ((g⁻¹)⁻¹ = g).

## Implementation Notes

The golden ratio φ is imported directly from `Mathlib.NumberTheory.Real.GoldenRatio`,
ensuring consistency with Mathlib's definition and enabling the use of existing lemmas
about algebraic properties of φ.

The primitive 5th root of unity ζ₅ is defined via complex exponential rather than
as a solution to x^5 = 1, which simplifies proofs about rotations.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.Definitions

open Real

/-- The four generators A, A⁻¹, B, B⁻¹ of the two-disk compound symmetry group. -/
inductive Generator where
  | A | Ainv | B | Binv
  deriving DecidableEq, Repr

/-- Inverse operation for generators.

The inverse of a generator is defined algebraically:
- A⁻¹ is the inverse of A (4th power, since A has order 5)
- B⁻¹ is the inverse of B (4th power, since B has order 5)
- Inverses are involutive: (A⁻¹)⁻¹ = A and (B⁻¹)⁻¹ = B

This instance allows using the standard `g⁻¹` notation for generators. -/
instance : Inv Generator where
  inv
    | .A => .Ainv
    | .Ainv => .A
    | .B => .Binv
    | .Binv => .B

/-- The inverse operation on generators is involutive. -/
@[simp]
lemma Generator.inv_inv (g : Generator) : g⁻¹⁻¹ = g := by
  cases g <;> rfl

/-- A word is a finite sequence of generators.

Words represent elements of the free group on two generators {A, B}.
In the two-disk compound symmetry group, not all formal words represent
distinct group elements (there are relations), but every group element
can be expressed as a word. -/
abbrev Word := List Generator

/-- The golden ratio φ = (1 + √5)/2.

This is the unique positive solution to x² = x + 1, and has the key property
that φ² = φ + 1. This algebraic relationship is central to the proof that
GG(5,5) is infinite at the critical radius.

We use Mathlib's definition to ensure compatibility with existing lemmas. -/
noncomputable def φ : ℝ := Real.goldenRatio

/-- The critical radius r_crit = √(3 + φ) ≈ 2.05817.

At this radius, the two disks of radius r_crit centered at ±1 overlap in a
specific way that creates a golden ratio relationship in the induced interval
exchange transformation. This causes a phase transition from finite to infinite
for the group GG(5,5).

For r < r_crit, the group GG(5,5) is finite.
For r > r_crit, the group GG(5,5) is also finite (with different structure).
Only at r = r_crit is the group infinite. -/
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
