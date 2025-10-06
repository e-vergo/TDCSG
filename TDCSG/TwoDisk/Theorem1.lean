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
  sorry

/-- Corollary: GG_5 has infinite members for some radius. -/
theorem GG5_has_infinite_member :
    ∃ r > 0, ∃ sys : TwoDiskSystem,
      sys.n₁ = 5 ∧ sys.n₂ = 5 ∧
      sys.r₁ = r ∧ sys.r₂ = r ∧
      sys.IsInfiniteGroup := by
  sorry

end TwoDiskSystem
