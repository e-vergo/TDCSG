import TDCSG.TwoDisk.Translations

/-!
# Theorem 1: Characterization of Infinite Two-Disk Groups

This file contains Theorem 1 from the paper, which characterizes exactly which
two-disk systems have infinite groups.

## Main theorem

* `theorem1`: GG_{n₁,n₂}(r) is infinite for some r iff lcm(n₁, n₂) ∉ {2,3,4,6}

## References

* Theorem 1 in "Two-Disk Compound Symmetry Groups" (lines 129-155)
-/

open Complex Nat

namespace TwoDiskSystem

/-- Theorem 1: A two-disk system has an infinite member if and only if
    lcm(n₁, n₂) is not in {2, 3, 4, 6}.

    This is closely related to the crystallographic restriction theorem. -/
theorem theorem1_sufficiency (sys : TwoDiskSystem)
    (h : Nat.lcm sys.n₁ sys.n₂ ∉ ({2, 3, 4, 6} : Set ℕ)) :
    ∃ r > 0, ∃ sys' : TwoDiskSystem,
      sys'.n₁ = sys.n₁ ∧ sys'.n₂ = sys.n₂ ∧
      sys'.r₁ = r ∧ sys'.r₂ = r ∧
      sys'.IsInfiniteGroup := by
  sorry

/-- The "only if" direction (stated but proof omitted in paper). -/
theorem theorem1_necessity (sys : TwoDiskSystem)
    (h : Nat.lcm sys.n₁ sys.n₂ ∈ ({2, 3, 4, 6} : Set ℕ)) :
    ∀ r > 0, ∀ sys' : TwoDiskSystem,
      sys'.n₁ = sys.n₁ → sys'.n₂ = sys.n₂ →
      sys'.r₁ = r → sys'.r₂ = r →
      sys'.IsFiniteGroup := by
  sorry

/-- Theorem 1 (full statement). -/
theorem theorem1 (sys : TwoDiskSystem) :
    (∃ r > 0, ∃ sys' : TwoDiskSystem,
      sys'.n₁ = sys.n₁ ∧ sys'.n₂ = sys.n₂ ∧
      sys'.r₁ = r ∧ sys'.r₂ = r ∧
      sys'.IsInfiniteGroup) ↔
    Nat.lcm sys.n₁ sys.n₂ ∉ ({2, 3, 4, 6} : Set ℕ) := by
  constructor
  · -- Forward direction: If there exists an infinite system, then lcm ∉ {2,3,4,6}
    intro ⟨r, hr, sys', h_n1, h_n2, h_r1, h_r2, h_inf⟩
    -- This is the necessity direction - would need crystallographic restriction
    sorry
  · -- Reverse direction: If lcm ∉ {2,3,4,6}, then there exists an infinite system
    exact theorem1_sufficiency sys

/-- Corollary: GG_5 has infinite members for some radius. -/
theorem GG5_has_infinite_member :
    ∃ r > 0, ∃ sys : TwoDiskSystem,
      sys.n₁ = 5 ∧ sys.n₂ = 5 ∧
      sys.r₁ = r ∧ sys.r₂ = r ∧
      sys.IsInfiniteGroup := by
  -- Create a system with n₁ = n₂ = 5
  let sys0 : TwoDiskSystem := {
    n₁ := 5
    n₂ := 5
    r₁ := 1  -- dummy radius
    r₂ := 1  -- dummy radius
    n₁_pos := by norm_num
    n₂_pos := by norm_num
    r₁_pos := by norm_num
    r₂_pos := by norm_num
  }
  -- lcm(5, 5) = 5 ∉ {2, 3, 4, 6}
  have h_lcm : Nat.lcm 5 5 ∉ ({2, 3, 4, 6} : Set ℕ)
  · simp only [Nat.lcm_self, Set.mem_insert_iff, Set.mem_singleton_iff]
    norm_num
  -- Apply theorem1_sufficiency
  obtain ⟨r, hr_pos, sys', h_n1, h_n2, h_r1, h_r2, h_inf⟩ := theorem1_sufficiency sys0 h_lcm
  use r, hr_pos, sys'

end TwoDiskSystem
