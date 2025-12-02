/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Circle

/-!
# Core Definitions for TDCSG

This file contains the fundamental constants and type aliases used throughout the TDCSG project.
All definitions here should be human-reviewable for mathematical correctness.

## Main definitions
- `φ` : The golden ratio (1 + √5)/2
- `r_crit` : The critical radius √(3 + φ)
- `Word` : Group words as lists of generator indices
-/

namespace TDCSG.Definitions

open Real

/-! ### Type Aliases -/

/-- Generator for the group action. -/
inductive Generator where
  | A | Ainv | B | Binv
  deriving DecidableEq, Repr

/-- Notation for generator inverses. -/
notation "A⁻¹" => Generator.Ainv
notation "B⁻¹" => Generator.Binv

/-- A word in generators A, B and their inverses. -/
abbrev Word := List Generator

/-! ### Core Constants -/

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def φ : ℝ := Real.goldenRatio

/-- The critical radius for GG5: r_crit = √(3 + φ). -/
noncomputable def r_crit : ℝ := Real.sqrt (3 + φ)

/-! ### 5th Roots of Unity -/

open scoped Complex
open Complex

/-- The primitive 5th root of unity: e^(2 pi i/5) -/
noncomputable def zeta5 : Complex := exp (2 * Real.pi * Complex.I / 5)

/-- Unicode alias for the primitive 5th root of unity -/
noncomputable abbrev ζ₅ : Complex := zeta5

/-- |ζ₅| = 1 -/
@[simp] lemma zeta5_abs : ‖ζ₅‖ = 1 := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * Real.pi * I / 5 = (2 * Real.pi / 5 : ℝ) * I by
    simp [div_eq_mul_inv]
    ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi / 5)

/-! ### Circle representation of ζ₅ -/

/-- ζ₅ as an element of the unit circle in ℂ.
    This leverages Mathlib's `Circle` type which provides group structure on unit complex numbers. -/
noncomputable def zeta5Circle : Circle :=
  ⟨ζ₅, mem_sphere_zero_iff_norm.2 zeta5_abs⟩

/-- The coercion of zeta5Circle back to ℂ is ζ₅. -/
@[simp]
lemma zeta5Circle_coe : (zeta5Circle : ℂ) = ζ₅ := rfl

/-- Powers of ζ₅ as Circle elements. -/
noncomputable def zeta5CirclePow (n : ℕ) : Circle := zeta5Circle ^ n

/-- ζ₅⁻¹ as a Circle element (equals ζ₅⁴ for clockwise rotation). -/
noncomputable def zeta5CircleInv : Circle := zeta5Circle⁻¹

/-- The coercion of zeta5CircleInv is ζ₅⁻¹. -/
@[simp]
lemma zeta5CircleInv_coe : (zeta5CircleInv : ℂ) = ζ₅⁻¹ := rfl

end TDCSG.Definitions
