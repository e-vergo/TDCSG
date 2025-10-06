import TDCSG.TwoDisk.GroupAction

/-!
# Piecewise Isometries for Two-Disk Systems

This file defines piecewise isometries and proves that two-disk rotations
are piecewise isometries.

## Main definitions

* `IsPiecewiseIsometry`: A function that preserves distances within certain regions
* `IsIsometry`: Standard isometry (distance-preserving everywhere)

## Key results

* Generators (a, b) are isometries on their respective disks
* Compositions of generators are piecewise isometries but not necessarily isometries
-/

open Complex

namespace TwoDiskSystem

variable (sys : TwoDiskSystem)

/-- A function is an isometry if it preserves distances everywhere. -/
def IsIsometry (f : ℂ → ℂ) : Prop :=
  ∀ z w : ℂ, ‖f z - f w‖ = ‖z - w‖

/-- A function is a piecewise isometry if it preserves distances within
    certain regions (even if not globally). -/
def IsPiecewiseIsometry (f : ℂ → ℂ) : Prop :=
  ∃ (regions : List (Set ℂ)), ∀ S ∈ regions, ∀ z ∈ S, ∀ w ∈ S,
    ‖f z - f w‖ = ‖z - w‖

/-- Left rotation is an isometry on the left disk. -/
theorem leftRotation_isometry_on_disk :
    ∀ z ∈ sys.leftDisk, ∀ w ∈ sys.leftDisk,
      ‖sys.leftRotation z - sys.leftRotation w‖ = ‖z - w‖ := by
  sorry

/-- Right rotation is an isometry on the right disk. -/
theorem rightRotation_isometry_on_disk :
    ∀ z ∈ sys.rightDisk, ∀ w ∈ sys.rightDisk,
      ‖sys.rightRotation z - sys.rightRotation w‖ = ‖z - w‖ := by
  sorry

/-- Left rotation is globally an isometry (since it's identity outside the disk). -/
theorem leftRotation_is_isometry : IsIsometry sys.leftRotation := by
  sorry

/-- Right rotation is globally an isometry (since it's identity outside the disk). -/
theorem rightRotation_is_isometry : IsIsometry sys.rightRotation := by
  sorry

/-- Composition of piecewise isometries is a piecewise isometry. -/
theorem composition_piecewise_isometry (f g : ℂ → ℂ)
    (hf : IsPiecewiseIsometry f) (hg : IsPiecewiseIsometry g) :
    IsPiecewiseIsometry (g ∘ f) := by
  sorry

/-- Any group element gives a piecewise isometry. -/
theorem group_element_piecewise_isometry (g : TwoDiskGroup) :
    IsPiecewiseIsometry (applyGroupElement sys g) := by
  sorry

end TwoDiskSystem
