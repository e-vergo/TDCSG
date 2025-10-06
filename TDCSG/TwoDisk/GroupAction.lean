import TDCSG.TwoDisk.Basic

/-!
# Group Actions for Two-Disk Systems

This file defines the group action of a two-disk system on the complex plane,
and key properties about orbits and finiteness.

## Main definitions

* `TwoDiskGroup`: The free group on two generators (a and b)
* `groupAction`: The action of the group on the complex plane
* `orbit`: The orbit of a point under the group action
* `IsFiniteGroup`: Whether the group acts with all finite orbits

## Key lemmas

* `points_stay_in_union`: Points moved by the group stay in the disk union
* `intersection_points_bounded`: Points in the intersection have bounded movement
-/

open Complex

namespace TwoDiskSystem

variable (sys : TwoDiskSystem)

/-- The free group on two generators, representing sequences of rotations.
    We use `FreeGroup (Fin 2)` where 0 represents the left rotation
    and 1 represents the right rotation. -/
abbrev TwoDiskGroup := FreeGroup (Fin 2)

/-- Apply a group element (sequence of rotations) to a point in the plane.
    TODO: Full implementation requires proper handling of FreeGroup structure. -/
noncomputable def applyGroupElement (sys : TwoDiskSystem) (g : TwoDiskGroup) (z : ℂ) : ℂ :=
  sorry

/-- The orbit of a point under the group action is the set of all points
    reachable by applying group elements. -/
def orbit (sys : TwoDiskSystem) (z : ℂ) : Set ℂ :=
  {w | ∃ g : TwoDiskGroup, applyGroupElement sys g z = w}

/-- A two-disk system has a finite group if all orbits are finite. -/
def IsFiniteGroup (sys : TwoDiskSystem) : Prop :=
  ∀ z : ℂ, Set.Finite (orbit sys z)

/-- A two-disk system has an infinite group if some orbit is infinite. -/
def IsInfiniteGroup (sys : TwoDiskSystem) : Prop :=
  ∃ z : ℂ, Set.Infinite (orbit sys z)

/-- Key lemma: If a point starts in the left disk, after left rotation
    it stays in the left disk. -/
lemma leftRotation_preserves_leftDisk (z : ℂ) (hz : z ∈ sys.leftDisk) :
    sys.leftRotation z ∈ sys.leftDisk := by
  sorry

/-- Key lemma: If a point starts in the right disk, after right rotation
    it stays in the right disk. -/
lemma rightRotation_preserves_rightDisk (z : ℂ) (hz : z ∈ sys.rightDisk) :
    sys.rightRotation z ∈ sys.rightDisk := by
  sorry

/-- If a point is not in a disk, the rotation for that disk leaves it unchanged. -/
lemma leftRotation_outside_leftDisk (z : ℂ) (hz : z ∉ sys.leftDisk) :
    sys.leftRotation z = z := by
  unfold leftRotation
  simp [hz]

/-- If a point is not in a disk, the rotation for that disk leaves it unchanged. -/
lemma rightRotation_outside_rightDisk (z : ℂ) (hz : z ∉ sys.rightDisk) :
    sys.rightRotation z = z := by
  unfold rightRotation
  simp [hz]

/-- General lemma: Points that are moved by the group stay within the disk union.
    This is a fundamental property that applies throughout the formalization. -/
theorem points_stay_in_union (z : ℂ) (g : TwoDiskGroup) :
    applyGroupElement sys g z ≠ z → applyGroupElement sys g z ∈ sys.diskUnion := by
  sorry

/-- If a point is in the intersection and we apply a bounded sequence of moves,
    it can stay in the intersection. This is crucial for Theorem 2. -/
theorem intersection_points_can_stay_bounded (z : ℂ) (hz : z ∈ sys.diskIntersection)
    (g : TwoDiskGroup) :
    applyGroupElement sys g z ∈ sys.diskUnion := by
  sorry

end TwoDiskSystem
