import TDCSG.Theory.GroupAction
import TDCSG.Theory.IsometrySimple

/-!
# Theorem 1: Crystallographic Restriction

This file contains Theorem 1 from the paper, which characterizes when
two-disk groups are finite.

## Main result

A two-disk group GG_{n₁,n₂}(r₁,r₂) is infinite if and only if the
disks overlap and neither (n₁,n₂) nor (n₂,n₁) is in the set
{(2,2), (2,3), (2,4), (2,5), (3,3)}.
-/

open TwoDiskSystem

namespace Theorem1

/-- The set of (n₁,n₂) pairs that give finite groups -/
def FinitePairs : Set (ℕ × ℕ) :=
  {(2,2), (2,3), (3,2), (2,4), (4,2), (2,5), (5,2), (3,3)}

/-- Theorem 1: Characterization of infinite two-disk groups -/
theorem two_disk_infinite_iff (sys : TwoDiskSystem) :
    (∃ g : TwoDiskGroup, g ≠ 1 ∧ ∀ n : ℕ, g^n ≠ 1) ↔
    sys.diskIntersection.Nonempty ∧
    (sys.n₁, sys.n₂) ∉ FinitePairs := by
  constructor
  · -- Forward direction: infinite group implies overlap and not in finite pairs
    intro ⟨g, hg_ne, hg_infinite⟩
    constructor
    · -- Must have overlap for non-trivial group
      sorry  -- Requires showing that without overlap, group is trivial
    · -- Must not be in finite pairs
      sorry  -- Crystallographic restriction theory
  · -- Backward direction: overlap and not in finite pairs implies infinite
    intro ⟨h_overlap, h_not_finite⟩
    -- This is the hard direction requiring the full machinery of the paper
    sorry  -- Main content of the paper

/-- Corollary: GG₅(r_c) is infinite -/
theorem GG5_infinite_at_critical :
    let sys : TwoDiskSystem := {
      n₁ := 5, n₂ := 5,
      r₁ := r_c, r₂ := r_c,
      n₁_pos := by norm_num,
      n₂_pos := by norm_num,
      r₁_pos := r_c_pos,
      r₂_pos := r_c_pos
    }
    ∃ g : TwoDiskGroup, g ≠ 1 ∧ ∀ n : ℕ, g^n ≠ 1 := by
  -- Apply Theorem 1
  rw [two_disk_infinite_iff]
  constructor
  · -- Show overlap at critical radius
    use 0
    unfold diskIntersection leftDisk rightDisk
    simp [Metric.mem_closedBall, leftCenter, rightCenter]
    constructor <;> {
      norm_num
      unfold r_c
      have : 1 < Real.sqrt (3 + goldenRatio) := by
        rw [Real.one_lt_sqrt (by linarith [goldenRatio_pos] : 0 ≤ 3 + goldenRatio)]
        linarith [one_lt_goldenRatio]
      linarith
    }
  · -- (5,5) is not in FinitePairs
    unfold FinitePairs
    simp

end Theorem1