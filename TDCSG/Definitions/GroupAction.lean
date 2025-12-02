import TDCSG.Definitions.Core
import TDCSG.Definitions.Geometry

namespace TDCSG.Definitions

open Real Complex
open scoped Circle

noncomputable def genA (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ leftDisk r then rotateAboutC leftCenter (-2 * π / 5) z else z

noncomputable def genB (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ rightDisk r then rotateAboutC rightCenter (-2 * π / 5) z else z

lemma genA_in_disk_eq_rotateAboutCircle (r : ℝ) (z : ℂ) (hz : z ∈ leftDisk r) :
    genA r z = rotateAboutCircle leftCenter (Circle.exp (-2 * π / 5)) z := by
  simp only [genA, hz, ↓reduceIte, rotateAboutCircle_eq_rotateAboutC]

lemma genB_in_disk_eq_rotateAboutCircle (r : ℝ) (z : ℂ) (hz : z ∈ rightDisk r) :
    genB r z = rotateAboutCircle rightCenter (Circle.exp (-2 * π / 5)) z := by
  simp only [genB, hz, ↓reduceIte, rotateAboutCircle_eq_rotateAboutC]

lemma genA_preserves_leftDisk (r : ℝ) (z : ℂ) (hz : z ∈ leftDisk r) :
    genA r z ∈ leftDisk r := by
  rw [genA_in_disk_eq_rotateAboutCircle r z hz]
  unfold leftDisk
  have h_center : leftCenter = (-1 : ℂ) := by unfold leftCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk (-1) _ r z hz

lemma genB_preserves_rightDisk (r : ℝ) (z : ℂ) (hz : z ∈ rightDisk r) :
    genB r z ∈ rightDisk r := by
  rw [genB_in_disk_eq_rotateAboutCircle r z hz]
  unfold rightDisk
  have h_center : rightCenter = (1 : ℂ) := by unfold rightCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk 1 _ r z hz

lemma Circle_exp_pow (theta : ℝ) (n : ℕ) : Circle.exp theta ^ n = Circle.exp (n * theta) := by
  induction n with
  | zero => simp [Circle.exp_zero]
  | succ n ih =>
    rw [pow_succ, ih, <- Circle.exp_add]
    congr 1
    push_cast
    ring

lemma circle_exp_neg_two_pi : Circle.exp (-2 * π) = 1 := by
  apply Subtype.ext
  simp only [Circle.coe_exp, Circle.coe_one]
  push_cast
  have h : (-2 : ℂ) * π * I = -(2 * π * I) := by ring
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

lemma Circle_exp_neg_two_pi_over_n_pow_n (n : ℕ) (hn : n ≥ 1) :
    Circle.exp (-2 * π / n) ^ n = 1 := by
  rw [Circle_exp_pow]
  have h : (n : ℝ) * (-2 * π / n) = -2 * π := by field_simp
  rw [h]
  exact circle_exp_neg_two_pi

lemma rotateAboutCircle_leftCenter_preserves_leftDisk (a : Circle) (r : ℝ) (z : ℂ)
    (hz : z ∈ leftDisk r) : rotateAboutCircle leftCenter a z ∈ leftDisk r := by
  unfold leftDisk
  have h_center : leftCenter = (-1 : ℂ) := by unfold leftCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk (-1) a r z hz

lemma rotateAboutCircle_rightCenter_preserves_rightDisk (a : Circle) (r : ℝ) (z : ℂ)
    (hz : z ∈ rightDisk r) : rotateAboutCircle rightCenter a z ∈ rightDisk r := by
  unfold rightDisk
  have h_center : rightCenter = (1 : ℂ) := by unfold rightCenter; simp
  rw [h_center]
  exact rotateAboutCircle_preserves_disk 1 a r z hz

lemma genA_n_outside (n : ℕ) (r : ℝ) (z : ℂ) (hz : z ∉ leftDisk r) :
    genA_n n r z = z := by
  unfold genA_n
  simp only [hz, if_false]

lemma genA_n_inside (n : ℕ) (r : ℝ) (z : ℂ) (hz : z ∈ leftDisk r) :
    genA_n n r z = rotateAboutCircle leftCenter (Circle.exp (-2 * π / n)) z := by
  unfold genA_n
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

lemma genB_n_outside (n : ℕ) (r : ℝ) (z : ℂ) (hz : z ∉ rightDisk r) :
    genB_n n r z = z := by
  unfold genB_n
  simp only [hz, if_false]

lemma genB_n_inside (n : ℕ) (r : ℝ) (z : ℂ) (hz : z ∈ rightDisk r) :
    genB_n n r z = rotateAboutCircle rightCenter (Circle.exp (-2 * π / n)) z := by
  unfold genB_n
  simp only [hz, if_true]
  rw [rotateAboutCircle_eq_rotateAboutC]

lemma rotateAboutCircle_leftCenter_iterate_preserves_leftDisk' (a : Circle) (r : ℝ) (k : ℕ)
    (w : ℂ) (hw : w ∈ leftDisk r) :
    (rotateAboutCircle leftCenter a)^[k] w ∈ leftDisk r := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact rotateAboutCircle_leftCenter_preserves_leftDisk a r _ ih

lemma rotateAboutCircle_rightCenter_iterate_preserves_rightDisk' (a : Circle) (r : ℝ) (k : ℕ)
    (w : ℂ) (hw : w ∈ rightDisk r) :
    (rotateAboutCircle rightCenter a)^[k] w ∈ rightDisk r := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact rotateAboutCircle_rightCenter_preserves_rightDisk a r _ ih

lemma genA_n_pow_n (n : ℕ) (hn : n ≥ 1) (r : ℝ) (z : ℂ) :
    (genA_n n r)^[n] z = z := by
  by_cases hz : z ∈ leftDisk r
  .
    set a := Circle.exp (-2 * π / n) with ha

    have h_eq_rot : forall k : ℕ, forall w : ℂ, w ∈ leftDisk r ->
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

    rw [rotateAboutCircle_pow]
    rw [ha, Circle_exp_neg_two_pi_over_n_pow_n n hn]
    exact rotateAboutCircle_one leftCenter z
  .
    have h_id : forall k : ℕ, (genA_n n r)^[k] z = z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ih]
        exact genA_n_outside n r z hz
    exact h_id n

lemma genB_n_pow_n (n : ℕ) (hn : n ≥ 1) (r : ℝ) (z : ℂ) :
    (genB_n n r)^[n] z = z := by
  by_cases hz : z ∈ rightDisk r
  .
    set a := Circle.exp (-2 * π / n) with ha

    have h_eq_rot : forall k : ℕ, forall w : ℂ, w ∈ rightDisk r ->
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

    rw [rotateAboutCircle_pow]
    rw [ha, Circle_exp_neg_two_pi_over_n_pow_n n hn]
    exact rotateAboutCircle_one rightCenter z
  .
    have h_id : forall k : ℕ, (genB_n n r)^[k] z = z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ih]
        exact genB_n_outside n r z hz
    exact h_id n

lemma iterate_split (f : ℂ -> ℂ) (n : ℕ) (hn : n ≥ 1) (x : ℂ) :
    f^[n] x = f^[n - 1] (f x) := by
  have h : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  conv_lhs => rw [h]
  rw [Function.iterate_succ_apply']
  exact (Function.Commute.iterate_self f (n - 1) x).symm

lemma iterate_unsplit (f : ℂ -> ℂ) (n : ℕ) (hn : n ≥ 1) (x : ℂ) :
    f (f^[n - 1] x) = f^[n] x := by
  have h : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  conv_rhs => rw [h]
  exact (Function.iterate_succ_apply' f (n - 1) x).symm

lemma genA_n_bijective (n : ℕ) (hn : n ≥ 1) (r : ℝ) : Function.Bijective (genA_n n r) := by

  have h_period : forall z, (genA_n n r)^[n] z = z := fun z => genA_n_pow_n n hn r z
  constructor
  .
    intro x y hxy

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
  .
    intro y
    use (genA_n n r)^[n - 1] y
    calc genA_n n r ((genA_n n r)^[n - 1] y)
        = (genA_n n r)^[n] y := iterate_unsplit (genA_n n r) n hn y
      _ = y := h_period y

lemma genB_n_bijective (n : ℕ) (hn : n ≥ 1) (r : ℝ) : Function.Bijective (genB_n n r) := by
  have h_period : forall z, (genB_n n r)^[n] z = z := fun z => genB_n_pow_n n hn r z
  constructor
  .
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
  .
    intro y
    use (genB_n n r)^[n - 1] y
    calc genB_n n r ((genB_n n r)^[n - 1] y)
        = (genB_n n r)^[n] y := iterate_unsplit (genB_n n r) n hn y
      _ = y := h_period y

noncomputable def applyGen (r : ℝ) (z : ℂ) : Generator → ℂ
  | .A    => genA r z
  | .Ainv => genA r (genA r (genA r (genA r z)))
  | .B    => genB r z
  | .Binv => genB r (genB r (genB r (genB r z)))

noncomputable def applyWord (r : ℝ) (w : Word) (z : ℂ) : ℂ :=
  w.foldl (applyGen r) z

noncomputable def orbit (r : ℝ) (z : ℂ) : Set ℂ :=
  { w | ∃ word : Word, applyWord r word z = w }

end TDCSG.Definitions
