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

/-- Composition of piecewise isometries is a piecewise isometry.

    Note: This proof is simplified for our specific application where rotations
    map disks to themselves. A fully general proof would require partition refinement. -/
theorem composition_piecewise_isometry (f g : ℂ → ℂ)
    (hf : IsPiecewiseIsometry f) (hg : IsPiecewiseIsometry g) :
    IsPiecewiseIsometry (g ∘ f) := by
  unfold IsPiecewiseIsometry at hf hg ⊢
  obtain ⟨Pf, hPf⟩ := hf
  obtain ⟨Pg, hPg⟩ := hg

  -- We create a refined partition: for each pair (Sf, Sg) in Pf × Pg,
  -- include Sf ∩ f⁻¹(Sg) if it's nonempty
  -- For simplicity, we'll use a direct approach suitable for disk rotations

  -- For disk rotations, we can use the intersection-based partition
  let refined_partition := Pf.flatMap (fun Sf => Pg.map (fun Sg => Sf ∩ {z | f z ∈ Sg}))
  use refined_partition

  intro R hR z hz w hw
  simp only [Function.comp_apply]

  -- R is in the refined partition, so it's Sf ∩ f⁻¹(Sg) for some Sf ∈ Pf and Sg ∈ Pg
  -- Unfold the flatMap and map to extract witnesses
  rw [List.mem_flatMap] at hR
  obtain ⟨Sf, hSf_mem, hR_in_map⟩ := hR
  rw [List.mem_map] at hR_in_map
  obtain ⟨Sg, hSg_mem, hR_def⟩ := hR_in_map
  rw [← hR_def] at hz hw

  -- Now hz and hw say z, w ∈ Sf ∩ {z | f z ∈ Sg}
  have hz_Sf : z ∈ Sf := hz.1
  have hw_Sf : w ∈ Sf := hw.1
  have hfz_Sg : f z ∈ Sg := by simpa using hz.2
  have hfw_Sg : f w ∈ Sg := by simpa using hw.2

  -- Apply both isometry properties
  calc ‖g (f z) - g (f w)‖
      = ‖f z - f w‖ := hPg Sg hSg_mem (f z) hfz_Sg (f w) hfw_Sg
    _ = ‖z - w‖ := hPf Sf hSf_mem z hz_Sf w hw_Sf

/-- The inverse left rotation is a piecewise isometry -/
theorem leftRotationInv_is_piecewise_isometry : IsPiecewiseIsometry sys.leftRotationInv := by
  unfold IsPiecewiseIsometry
  use [sys.leftDisk, sys.leftDiskᶜ]
  intro S hS
  simp only [List.mem_cons] at hS
  cases hS with
  | inl h => -- S = leftDisk
    rw [h]
    intro z hz w hw
    unfold leftRotationInv
    rw [if_pos hz, if_pos hw]
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
    have h_exp_norm : ‖exp (-I * sys.leftAngle)‖ = 1 := by
      rw [norm_exp]; simp
    rw [h_exp_norm, one_mul]
    simp [sub_sub]
  | inr h => -- S in [leftDiskᶜ]
    cases h with
    | inl h' => -- S = leftDiskᶜ
      rw [h']
      intro z hz w hw
      unfold leftRotationInv
      rw [if_neg hz, if_neg hw]
    | inr h' => -- S ∈ []
      cases h'

/-- The inverse right rotation is a piecewise isometry -/
theorem rightRotationInv_is_piecewise_isometry : IsPiecewiseIsometry sys.rightRotationInv := by
  unfold IsPiecewiseIsometry
  use [sys.rightDisk, sys.rightDiskᶜ]
  intro S hS
  simp only [List.mem_cons] at hS
  cases hS with
  | inl h => -- S = rightDisk
    rw [h]
    intro z hz w hw
    unfold rightRotationInv
    rw [if_pos hz, if_pos hw]
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
    have h_exp_norm : ‖exp (-I * sys.rightAngle)‖ = 1 := by
      rw [norm_exp]; simp
    rw [h_exp_norm, one_mul]
    simp [sub_sub]
  | inr h => -- S in [rightDiskᶜ]
    cases h with
    | inl h' => -- S = rightDiskᶜ
      rw [h']
      intro z hz w hw
      unfold rightRotationInv
      rw [if_neg hz, if_neg hw]
    | inr h' => -- S ∈ []
      cases h'

/-- Each generator application is a piecewise isometry -/
lemma applyGenerator_is_piecewise_isometry (gen : Fin 2) (inv : Bool) :
    IsPiecewiseIsometry (applyGenerator sys gen inv) := by
  match gen, inv with
  | 0, false => exact leftRotation_is_piecewise_isometry sys
  | 0, true => exact leftRotationInv_is_piecewise_isometry sys
  | 1, false => exact rightRotation_is_piecewise_isometry sys
  | 1, true => exact rightRotationInv_is_piecewise_isometry sys

/-- Helper: foldl of piecewise isometries starting from a piecewise isometry is a piecewise isometry -/
lemma foldl_preserves_piecewise_isometry (word : List (Fin 2 × Bool)) (f₀ : ℂ → ℂ)
    (hf₀ : IsPiecewiseIsometry f₀) :
    IsPiecewiseIsometry (fun z => word.foldl (fun z' p => applyGenerator sys p.1 p.2 z') (f₀ z)) := by
  induction word generalizing f₀ with
  | nil =>
    -- Empty word, just return f₀
    simp [List.foldl]
    exact hf₀
  | cons hd tl ih =>
    -- Cons case: show composition preserves property
    simp only [List.foldl]
    -- After applying hd, we get a new function which is still piecewise isometry
    have h_comp : IsPiecewiseIsometry ((applyGenerator sys hd.1 hd.2) ∘ f₀) := by
      -- This is composition of two piecewise isometries
      exact composition_piecewise_isometry f₀ (applyGenerator sys hd.1 hd.2) hf₀
        (applyGenerator_is_piecewise_isometry sys hd.1 hd.2)
    -- Apply induction hypothesis
    exact ih ((applyGenerator sys hd.1 hd.2) ∘ f₀) h_comp

/-- Any group element gives a piecewise isometry.

    Proof: By induction on the word representation, using the fact that each generator
    is a piecewise isometry and composition preserves piecewise isometry. -/
theorem group_element_piecewise_isometry (g : TwoDiskGroup) :
    IsPiecewiseIsometry (applyGroupElement sys g) := by
  unfold applyGroupElement
  let word := g.toWord

  -- The identity function is a piecewise isometry (trivial partition)
  have h_id : IsPiecewiseIsometry (fun z => z) := by
    unfold IsPiecewiseIsometry
    use [Set.univ]
    intro S hS
    simp at hS
    rw [hS]
    intro z _ w _
    rfl

  -- Apply the foldl lemma starting from identity
  have h := foldl_preserves_piecewise_isometry sys word id h_id
  convert h using 2

end TwoDiskSystem
