import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Basic test file for BFS-Prover

Simple theorems to test tactic generation.
-/

namespace TDCSG

-- Simple theorem for testing
theorem add_comm (n m : ℕ) : n + m = m + n := by
  sorry

-- Another simple one
theorem zero_add (n : ℕ) : 0 + n = n := by
  sorry

-- Slightly more complex
theorem succ_add (n m : ℕ) : n.succ + m = (n + m).succ := by
  sorry

end TDCSG
