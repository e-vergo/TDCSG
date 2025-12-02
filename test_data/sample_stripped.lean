import Mathlib.Data.Real.Basic

namespace Test

def addTwo (x : ℕ) : ℕ := x + 2

lemma addTwo_pos (x : ℕ) : addTwo x > x := by
  unfold addTwo
  omega

lemma unusedLemma : 1 + 1 = 2 := by
  norm_num

theorem addTwo_injective : ∀ x y, addTwo x = addTwo y → x = y := by
  intro x y h
  unfold addTwo at h
  omega

end Test
