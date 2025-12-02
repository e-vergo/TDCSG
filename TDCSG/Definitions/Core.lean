import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Circle

namespace TDCSG.Definitions

open Real

inductive Generator where
  | A | Ainv | B | Binv
  deriving DecidableEq, Repr

notation "A⁻¹" => Generator.Ainv
notation "B⁻¹" => Generator.Binv

abbrev Word := List Generator

noncomputable def φ : ℝ := Real.goldenRatio

noncomputable def r_crit : ℝ := Real.sqrt (3 + φ)

open scoped Complex
open Complex

noncomputable def zeta5 : Complex := exp (2 * Real.pi * Complex.I / 5)

noncomputable abbrev ζ₅ : Complex := zeta5

@[simp] lemma zeta5_abs : ‖ζ₅‖ = 1 := by
  unfold ζ₅ zeta5
  rw [show (2 : ℂ) * Real.pi * I / 5 = (2 * Real.pi / 5 : ℝ) * I by
    simp [div_eq_mul_inv]
    ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi / 5)

noncomputable def zeta5Circle : Circle :=
  ⟨ζ₅, mem_sphere_zero_iff_norm.2 zeta5_abs⟩

@[simp]
lemma zeta5Circle_coe : (zeta5Circle : ℂ) = ζ₅ := rfl

noncomputable def zeta5CirclePow (n : ℕ) : Circle := zeta5Circle ^ n

noncomputable def zeta5CircleInv : Circle := zeta5Circle⁻¹

@[simp]
lemma zeta5CircleInv_coe : (zeta5CircleInv : ℂ) = ζ₅⁻¹ := rfl

end TDCSG.Definitions
