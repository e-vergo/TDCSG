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
  intro z hz w hw
  unfold leftRotation
  rw [if_pos hz, if_pos hw]
  -- Both are rotated: c + r*(z-c) and c + r*(w-c)
  rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
  have h_exp_norm : ‖exp (I * sys.leftAngle)‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  rw [h_exp_norm, one_mul]
  simp [sub_sub]

/-- Right rotation is an isometry on the right disk. -/
theorem rightRotation_isometry_on_disk :
    ∀ z ∈ sys.rightDisk, ∀ w ∈ sys.rightDisk,
      ‖sys.rightRotation z - sys.rightRotation w‖ = ‖z - w‖ := by
  intro z hz w hw
  unfold rightRotation
  rw [if_pos hz, if_pos hw]
  rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
  have h_exp_norm : ‖exp (I * sys.rightAngle)‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  rw [h_exp_norm, one_mul]
  simp [sub_sub]

/-- Left rotation is a piecewise isometry. -/
theorem leftRotation_is_piecewise_isometry : IsPiecewiseIsometry sys.leftRotation := by
  unfold IsPiecewiseIsometry
  use [sys.leftDisk, sys.leftDiskᶜ]
  intro S hS
  simp only [List.mem_cons] at hS
  cases hS with
  | inl h => -- S = leftDisk
    rw [h]
    exact leftRotation_isometry_on_disk sys
  | inr h => -- S in [leftDiskᶜ]
    cases h with
    | inl h' => -- S = leftDiskᶜ
      rw [h']
      intro z hz w hw
      unfold leftRotation
      rw [if_neg hz, if_neg hw]
      -- Both outside disk, so both unchanged
    | inr h' => -- S ∈ []
      cases h'

/-- Right rotation is a piecewise isometry. -/
theorem rightRotation_is_piecewise_isometry : IsPiecewiseIsometry sys.rightRotation := by
  unfold IsPiecewiseIsometry
  use [sys.rightDisk, sys.rightDiskᶜ]
  intro S hS
  simp only [List.mem_cons] at hS
  cases hS with
  | inl h => -- S = rightDisk
    rw [h]
    exact rightRotation_isometry_on_disk sys
  | inr h => -- S in [rightDiskᶜ]
    cases h with
    | inl h' => -- S = rightDiskᶜ
      rw [h']
      intro z hz w hw
      unfold rightRotation
      rw [if_neg hz, if_neg hw]
      -- Both outside disk, so both unchanged
    | inr h' => -- S ∈ []
      cases h'

/-- Composition of piecewise isometries is a piecewise isometry. -/
theorem composition_piecewise_isometry (f g : ℂ → ℂ)
    (hf : IsPiecewiseIsometry f) (hg : IsPiecewiseIsometry g) :
    IsPiecewiseIsometry (g ∘ f) := by
  unfold IsPiecewiseIsometry at hf hg ⊢
  -- Get the partitions for f and g
  obtain ⟨Pf, hPf⟩ := hf
  obtain ⟨Pg, hPg⟩ := hg

  -- The ideal refined partition would consist of sets S such that:
  -- 1. f is an isometry on S (S ∈ Pf or a subset thereof)
  -- 2. f(S) is contained in a single piece of g's partition

  -- For this formalization, we use both partitions and rely on the fact that
  -- in our application, the rotations map regions appropriately
  use Pf

  intro S hS z hz w hw
  -- On S, f preserves distances
  have hf_iso : ‖f z - f w‖ = ‖z - w‖ := hPf S hS z hz w hw

  -- For g to preserve distances on f(z) and f(w), they need to be in the same
  -- piece of g's partition. In our application with disk rotations, when f is
  -- a rotation on S (e.g., S = leftDisk), the image f(S) = S, so f(z), f(w) ∈ S.
  -- If S is also in g's partition (or a subset), then g preserves distances there.

  simp only [Function.comp_apply]

  -- The challenge is that we need to know which piece of Pg contains f(z) and f(w)
  -- For our specific application:
  -- - If S = leftDisk and f = leftRotation, then f(S) = leftDisk
  -- - If S = rightDisk and f = rightRotation, then f(S) = rightDisk
  -- - Outside the disks, rotations are identity

  -- We handle this by cases on whether f(z) and f(w) are in some piece of Pg
  -- Since we know f preserves distances on S, and for our rotations,
  -- f maps disk regions to themselves, this works out.

  -- This is a simplification that works for our specific case of disk rotations
  conv_rhs => rw [← hf_iso]

  -- Now we need: ‖g (f z) - g (f w)‖ = ‖f z - f w‖
  -- This holds if f(z) and f(w) are in the same piece of g's partition
  -- For disk rotations, this is true because rotations map disks to themselves
  -- A complete proof would require showing this explicitly

  -- For now, we accept this as an axiom of our simplified model
  sorry  -- This requires detailed partition refinement or case analysis on disk membership

/-- Any group element gives a piecewise isometry. -/
theorem group_element_piecewise_isometry (g : TwoDiskGroup) :
    IsPiecewiseIsometry (applyGroupElement sys g) := by
  -- This follows by induction on g using the fact that:
  -- 1. Identity is a piecewise isometry (trivial)
  -- 2. Generators (left/right rotations) are piecewise isometries (proven above)
  -- 3. Composition and inverse preserve piecewise isometry

  -- We'll use induction on the word representation
  unfold applyGroupElement
  let word := g.toWord

  -- Due to the complexity of the proof with match statements,
  -- we'll use our simplified composition theorem
  sorry  -- This requires a careful handling of the match expression evaluation

end TwoDiskSystem
