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

/-- Apply a single generator or its inverse to a point -/
noncomputable def applyGenerator (sys : TwoDiskSystem) (i : Fin 2) (inv : Bool) (z : ℂ) : ℂ :=
  match i, inv with
  | 0, false => sys.leftRotation z
  | 0, true => sys.leftRotationInv z
  | 1, false => sys.rightRotation z
  | 1, true => sys.rightRotationInv z

/-- Apply a group element (sequence of rotations) to a point in the plane.
    This is implemented by converting to the reduced word representation
    and applying rotations sequentially.
    - FreeGroup.of 0 maps to leftRotation
    - FreeGroup.of 1 maps to rightRotation
    - Multiplication in the group corresponds to function composition
    - Inverses correspond to inverse rotations -/
noncomputable def applyGroupElement (sys : TwoDiskSystem) (g : TwoDiskGroup) (z : ℂ) : ℂ :=
  let word := g.toWord
  word.foldl (fun z' (gen, inv) => applyGenerator sys gen inv z') z

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
  unfold leftRotation
  simp only [leftDisk] at hz ⊢
  rw [if_pos hz]
  simp only [Metric.mem_closedBall]
  rw [dist_comm, Complex.dist_eq]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_mul]
  have h_exp_norm : ‖exp (I * sys.leftAngle)‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  rw [h_exp_norm, one_mul]
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  exact hz

/-- Key lemma: If a point starts in the right disk, after right rotation
    it stays in the right disk. -/
lemma rightRotation_preserves_rightDisk (z : ℂ) (hz : z ∈ sys.rightDisk) :
    sys.rightRotation z ∈ sys.rightDisk := by
  unfold rightRotation
  simp only [rightDisk] at hz ⊢
  rw [if_pos hz]
  simp only [Metric.mem_closedBall]
  rw [dist_comm, Complex.dist_eq]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_mul]
  have h_exp_norm : ‖exp (I * sys.rightAngle)‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  rw [h_exp_norm, one_mul]
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  exact hz

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

/-- Helper: Each generator preserves membership in diskUnion -/
lemma applyGenerator_preserves_union (gen : Fin 2) (inv : Bool) (z : ℂ) :
    z ∈ sys.diskUnion → applyGenerator sys gen inv z ∈ sys.diskUnion := by
  intro hz
  unfold applyGenerator
  match gen, inv with
  | 0, false =>
    -- leftRotation
    unfold leftRotation
    split_ifs with h
    · -- z ∈ leftDisk, rotation keeps it in leftDisk
      left
      unfold leftDisk at h ⊢
      simp only [Metric.mem_closedBall] at h ⊢
      rw [dist_comm, Complex.dist_eq]
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_mul]
      have h_exp_norm : ‖exp (I * sys.leftAngle)‖ = 1 := by
        rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
      rw [h_exp_norm, one_mul]
      rw [← Complex.dist_eq]
      exact h
    · -- z ∉ leftDisk, stays unchanged
      exact hz
  | 0, true =>
    -- leftRotationInv
    unfold leftRotationInv
    split_ifs with h
    · -- z ∈ leftDisk, inverse rotation keeps it in leftDisk
      left
      -- Need to prove leftRotationInv preserves leftDisk
      unfold leftDisk at h ⊢
      simp only [Metric.mem_closedBall] at h ⊢
      rw [dist_comm, Complex.dist_eq]
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_mul]
      have h_exp_norm : ‖exp (-I * sys.leftAngle)‖ = 1 := by
        rw [norm_exp]
        simp
      rw [h_exp_norm, one_mul]
      rw [← Complex.dist_eq]
      exact h
    · exact hz
  | 1, false =>
    -- rightRotation
    unfold rightRotation
    split_ifs with h
    · -- z ∈ rightDisk, rotation keeps it in rightDisk
      right
      unfold rightDisk at h ⊢
      simp only [Metric.mem_closedBall] at h ⊢
      rw [dist_comm, Complex.dist_eq]
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_mul]
      have h_exp_norm : ‖exp (I * sys.rightAngle)‖ = 1 := by
        rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
      rw [h_exp_norm, one_mul]
      rw [← Complex.dist_eq]
      exact h
    · exact hz
  | 1, true =>
    -- rightRotationInv
    unfold rightRotationInv
    split_ifs with h
    · -- z ∈ rightDisk, inverse rotation keeps it in rightDisk
      right
      unfold rightDisk at h ⊢
      simp only [Metric.mem_closedBall] at h ⊢
      rw [dist_comm, Complex.dist_eq]
      rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_mul]
      have h_exp_norm : ‖exp (-I * sys.rightAngle)‖ = 1 := by
        rw [norm_exp]
        simp
      rw [h_exp_norm, one_mul]
      rw [← Complex.dist_eq]
      exact h
    · exact hz

/-- General lemma: Points that are moved by the group stay within the disk union.
    This is a fundamental property that applies throughout the formalization. -/
theorem points_stay_in_union (z : ℂ) (g : TwoDiskGroup) :
    applyGroupElement sys g z ≠ z → applyGroupElement sys g z ∈ sys.diskUnion := by
  intro h_moved
  -- The key insight: rotations only move points within their respective disks,
  -- and leave other points unchanged. So any moved point must be in one of the disks,
  -- and the result will also be in the disk union.
  sorry  -- This requires a proper induction on the FreeGroup structure

/-- If a point is in the intersection and we apply a bounded sequence of moves,
    it can stay in the intersection. This is crucial for Theorem 2. -/
theorem intersection_points_can_stay_bounded (z : ℂ) (hz : z ∈ sys.diskIntersection)
    (g : TwoDiskGroup) :
    applyGroupElement sys g z ∈ sys.diskUnion := by
  -- If z is in the intersection, it's in both disks, hence in the union
  have h_z_in_union : z ∈ sys.diskUnion := by
    unfold diskIntersection at hz
    simp only [Set.mem_inter_iff] at hz
    left
    exact hz.1
  -- The result follows from the preservation lemma
  sorry  -- Need proper induction on FreeGroup structure

end TwoDiskSystem
