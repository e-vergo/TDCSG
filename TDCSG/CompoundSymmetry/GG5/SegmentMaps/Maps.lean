/-
Copyright (c) 2025-10-18. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

import TDCSG.CompoundSymmetry.GG5.SegmentMaps.Generators
import TDCSG.CompoundSymmetry.GG5.SegmentMaps.DiskPreservation

/-!
# GG5 Transformation Maps

This file defines the three key transformations (map1, map2, map3) that partition
the segment E'E and proves they are bijective mappings to other segments.

## Main Definitions

- `map1`: E'F' → GF (composition: genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv ∘ genA_inv)
- `map2`: F'G  → FE (composition: genB ∘ genB ∘ genA ∘ genB ∘ genA)
- `map3`: G'E  → E'G (composition: genB_inv ∘ genA_inv ∘ genB_inv ∘ genA ∘ genB ∘ genA)

These transformations establish the interval exchange at the heart of Theorem 2.

## Main Results

- `map1_bijection_E'F'_to_GF`: Bijection from segment E'F' to GF
- `map2_bijection_FpG_to_FE`: Bijection from segment F'G to FE
- `map3_bijection_GpE_to_E'G`: Bijection from segment G'E to E'G

## Implementation Notes

The main computational challenge is verifying the endpoint mappings, which require
extensive symbolic computation with the 5th root of unity ζ₅. Several endpoint
proofs are marked with `sorry` to enable incremental development.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real

/-! ### Map Definitions -/

/--
First critical transformation a⁻²b⁻¹a⁻¹b⁻¹ mapping segment E'F to GF.
-/
noncomputable def map1 : ℂ → ℂ :=
  genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv ∘ genA_inv

/--
Second critical transformation abab² mapping segment F'G to FE.
-/
noncomputable def map2 : ℂ → ℂ :=
  genB ∘ genB ∘ genA ∘ genB ∘ genA

/--
Third critical transformation abab⁻¹a⁻¹b⁻¹ mapping segment G'E to E'G.
-/
noncomputable def map3 : ℂ → ℂ :=
  genB_inv ∘ genA_inv ∘ genB_inv ∘ genA ∘ genB ∘ genA

/-! ### Isometry Infrastructure

These lemmas capture the general principle that an isometry mapping the endpoints
of a segment also maps the segment bijectively with preserved parameterization.

The key challenge is proving that for an isometry f with f(A) = C and f(B) = D,
we have: f(A + t•(B - A)) = C + t•(D - C) for all t ∈ [0,1].

**PROOF STRATEGY FOR FUTURE COMPLETION:**

The proof requires several Mathlib ingredients:
1. Segment characterization: Points on [A,B] are exactly {A + t•(B-A) | t ∈ [0,1]}
2. Distance tripartition: If dist(A,P) + dist(P,B) = dist(A,B), then P ∈ [A,B]
3. Isometry preserves: dist(f(A), f(P)) = dist(A,P)
4. Uniqueness: Given the distances, parameter t is determined uniquely

The proof flow:
- For p = A + t•(B-A), compute dist(A,p) = t·dist(A,B)
- Apply isometry: dist(C, f(p)) = dist(A,p) = t·dist(A,B) = t·dist(C,D)
- Similarly: dist(f(p), D) = (1-t)·dist(C,D)
- Distance equation: dist(C, f(p)) + dist(f(p), D) = dist(C,D)
- Conclude: f(p) lies on [C,D] with parameter s satisfying dist(C, f(p)) = s·dist(C,D)
- Therefore: s = t, so f(p) = C + t•(D-C)

**IMPLEMENTATION NOTES:**

This is currently left as sorry to avoid blocking progress. The bijection proofs
inline the strategy above. If this general lemma proves too difficult (>3 hours),
it's acceptable to inline the reasoning in each of the three bijection proofs.
-/

/-- If an isometry maps the endpoints of a segment to the endpoints of another segment,
    then it maps the first segment bijectively to the second, preserving parameterization.

    This is a key infrastructure lemma for proving that map1, map2, map3 implement
    the interval exchange transformation described in Theorem 2. -/
lemma isometry_maps_segment_bij (f : ℂ → ℂ) (A B C D : ℂ)
    (hiso : ∀ z w, ‖f z - f w‖ = ‖z - w‖)
    (hA : f A = C) (hB : f B = D)
    (hAB : A ≠ B) (hCD : C ≠ D) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃! s ∈ Set.Icc (0 : ℝ) 1,
        f (A + t • (B - A)) = C + s • (D - C) := by
  -- PROOF STRATEGY (see documentation above)
  -- This requires Mathlib lemmas about:
  -- - Segment characterization via parameters
  -- - Distance characterization of points on segments
  -- - Uniqueness from distance constraints
  -- Currently marked sorry to unblock Phase 2 endpoint computations
  sorry

/-! ### Helper Points

These points serve as endpoints for the three segments in the interval exchange.
-/

/--
F' defined as the reflection of F through the origin.
This is the starting point of the second segment in the interval exchange.
-/
noncomputable def F' : ℂ := -F

/--
G' defined as the reflection of G through the origin.
This is the starting point of the third segment in the interval exchange.
-/
noncomputable def G' : ℂ := -G

/-! ### Segment Helper Lemmas

These lemmas establish that various segments and their endpoints lie in the
disk intersection, which is necessary for applying the generator transformations.
-/

/--
Points on segment [E', F] lie in the disk intersection.
-/
lemma segment_E'F_in_intersection (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let p := E' + t • (F - E')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  -- Both E' and F lie on segment [E', E]
  -- E' is an endpoint (t=0)
  -- F is at parameter (1 + √5)/4
  -- So E' + t•(F - E') with t ∈ [0,1] traces a subsegment of [E', E]
  have hF := F_on_segment_E'E
  obtain ⟨t_F, htF0, htF1, hF_eq⟩ := hF
  -- The point p = E' + t•(F - E') can be rewritten as
  -- p = E' + t•(F - E') = E' + t•((E' + t_F•(E - E')) - E')
  --   = E' + t•t_F•(E - E')
  --   = E' + (t•t_F)•(E - E')
  -- So p is on segment [E', E] with parameter t•t_F
  have hp : p = E' + (t * t_F) • (E - E') := by
    calc p = E' + t • (F - E') := rfl
      _ = E' + t • ((E' + t_F • (E - E')) - E') := by rw [← hF_eq]
      _ = E' + t • (t_F • (E - E')) := by ring_nf
      _ = E' + (t * t_F) • (E - E') := by rw [smul_smul]
  rw [hp]
  apply segment_in_disk_intersection
  constructor
  · apply mul_nonneg ht0 htF0
  · calc t * t_F ≤ 1 * t_F := by
        { apply mul_le_mul_of_nonneg_right ht1 htF0 }
      _ = t_F := by ring
      _ ≤ 1 := htF1

/--
Points on segment [G, F] lie in the disk intersection.
-/
lemma segment_GF_in_intersection (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let q := G + s • (F - G)
    ‖q + 1‖ ≤ r_crit ∧ ‖q - 1‖ ≤ r_crit := by
  intro q
  -- Both G and F lie on segment [E', E]
  -- G is at parameter (√5 - 1)/2
  -- F is at parameter (1 + √5)/4
  -- The segment [G, F] is a subsegment of [E', E]
  have hG := G_on_segment_E'E
  have hF := F_on_segment_E'E
  obtain ⟨t_G, htG0, htG1, hG_eq⟩ := hG
  obtain ⟨t_F, htF0, htF1, hF_eq⟩ := hF
  -- q = G + s•(F - G) = (1-s)•G + s•F
  -- Since G and F are both on [E', E], their convex combination is too
  -- q = (1-s)•(E' + t_G•(E - E')) + s•(E' + t_F•(E - E'))
  --   = E' + ((1-s)•t_G + s•t_F)•(E - E')
  have hq : q = E' + ((1 - s) * t_G + s * t_F) • (E - E') := by
    calc q = G + s • (F - G) := rfl
      _ = (1 - s) • G + s • F := by module
      _ = (1 - s) • (E' + t_G • (E - E')) + s • (E' + t_F • (E - E')) := by
        rw [← hG_eq, ← hF_eq]
      _ = E' + ((1 - s) * t_G + s * t_F) • (E - E') := by
        simp only [smul_add, smul_smul]
        module
  rw [hq]
  apply segment_in_disk_intersection
  constructor
  · -- Show 0 ≤ (1 - s) * t_G + s * t_F
    apply add_nonneg
    · apply mul_nonneg; linarith; exact htG0
    · apply mul_nonneg hs0 htF0
  · -- Show (1 - s) * t_G + s * t_F ≤ 1
    -- We have t_G ≤ 1 and t_F ≤ 1
    -- So (1 - s) * t_G + s * t_F ≤ (1 - s) * 1 + s * 1 = 1
    calc (1 - s) * t_G + s * t_F
        ≤ (1 - s) * 1 + s * 1 := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left htG1
            linarith
          · apply mul_le_mul_of_nonneg_left htF1 hs0
      _ = 1 := by ring

/--
F' lies in the disk intersection.
-/
lemma F'_in_disk_intersection : ‖F' + 1‖ ≤ r_crit ∧ ‖F' - 1‖ ≤ r_crit := by
  unfold F'
  have hF := F_on_segment_E'E
  obtain ⟨t, ht0, ht1, hF_eq⟩ := hF
  -- F = E' + t•(E - E'), so -F = -(E' + t•(E - E'))
  -- Since the disk intersection is symmetric about the origin
  -- (both disk centers ±1 are symmetric), -F is also in the intersection
  constructor
  · -- Show ‖-F + 1‖ ≤ r_crit
    rw [show (-F : ℂ) + 1 = -(F - 1) by ring, norm_neg]
    -- F is in the right disk, so ‖F - 1‖ ≤ r_crit
    rw [hF_eq]
    have : ‖E' + t • (E - E') - 1‖ ≤ r_crit :=
      (segment_in_disk_intersection t ⟨ht0, ht1⟩).2
    exact this
  · -- Show ‖-F - 1‖ ≤ r_crit
    rw [show (-F : ℂ) - 1 = -(F + 1) by ring, norm_neg]
    -- F is in the left disk, so ‖F + 1‖ ≤ r_crit
    rw [hF_eq]
    have : ‖E' + t • (E - E') + 1‖ ≤ r_crit :=
      (segment_in_disk_intersection t ⟨ht0, ht1⟩).1
    exact this

/--
Points on segment [E', F'] lie in the disk intersection.
-/
lemma segment_E'F'_in_intersection (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let p := E' + t • (F' - E')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  -- Both E' and F' lie in the disk intersection
  -- The disk intersection is convex, so the segment [E', F'] is also in it
  have hE' : ‖E' + 1‖ ≤ r_crit ∧ ‖E' - 1‖ ≤ r_crit := by
    constructor
    · rw [show E' + 1 = E' - (-1 : ℂ) by ring]
      exact E'_in_left_disk
    · rw [show E' - 1 = -(E - (-1 : ℂ)) by unfold E'; ring]
      rw [norm_neg, show E - -1 = E + 1 by ring]
      exact E_on_left_disk_boundary.le
  have hF' := F'_in_disk_intersection
  -- Use convexity of closed balls
  have hp_segment : p ∈ segment ℝ E' F' := by
    use (1 - t), t
    constructor; · linarith [ht0]
    constructor; · exact ht0
    constructor; · linarith [ht1]
    calc (1 - t) • E' + t • F'
        = E' - t • E' + t • F' := by rw [sub_smul, one_smul]
      _ = E' + (t • F' - t • E') := by ring
      _ = E' + t • (F' - E') := by rw [smul_sub]
  constructor
  · -- Left disk
    have h_E'_in_left : E' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (E' - (-1) : ℂ) = E' + 1 by ring]
      exact hE'.1
    have h_F'_in_left : F' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (F' - (-1) : ℂ) = F' + 1 by ring]
      exact hF'.1
    have h_convex : Convex ℝ (Metric.closedBall ((-1) : ℂ) r_crit) :=
      convex_closedBall ((-1) : ℂ) r_crit
    have h_segment_subset : segment ℝ E' F' ⊆ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_convex.segment_subset h_E'_in_left h_F'_in_left
    have hp_in_left : p ∈ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_left
    simp only [dist_eq_norm] at hp_in_left
    rw [show (p - (-1) : ℂ) = p + 1 by ring] at hp_in_left
    exact hp_in_left
  · -- Right disk
    have h_E'_in_right : E' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hE'.2
    have h_F'_in_right : F' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hF'.2
    have h_convex : Convex ℝ (Metric.closedBall (1 : ℂ) r_crit) :=
      convex_closedBall (1 : ℂ) r_crit
    have h_segment_subset : segment ℝ E' F' ⊆ Metric.closedBall (1 : ℂ) r_crit :=
      h_convex.segment_subset h_E'_in_right h_F'_in_right
    have hp_in_right : p ∈ Metric.closedBall (1 : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_right
    simp only [dist_eq_norm] at hp_in_right
    exact hp_in_right

/--
G lies in the disk intersection.
-/
lemma G_in_disk_intersection : ‖G + 1‖ ≤ r_crit ∧ ‖G - 1‖ ≤ r_crit := by
  have hG := G_on_segment_E'E
  obtain ⟨t, ht0, ht1, hG_eq⟩ := hG
  rw [hG_eq]
  exact segment_in_disk_intersection t ⟨ht0, ht1⟩

/--
Points on segment [F', G] lie in the disk intersection.
-/
lemma segment_F'G_in_intersection (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let p := F' + t • (G - F')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  -- Both F' and G lie in the disk intersection
  -- The disk intersection is convex, so the segment [F', G] is also in it
  have hF' := F'_in_disk_intersection
  have hG := G_in_disk_intersection
  -- Use convexity of closed balls
  have hp_segment : p ∈ segment ℝ F' G := by
    use (1 - t), t
    constructor; · linarith [ht0]
    constructor; · exact ht0
    constructor; · linarith [ht1]
    calc (1 - t) • F' + t • G
        = F' - t • F' + t • G := by rw [sub_smul, one_smul]
      _ = F' + (t • G - t • F') := by ring
      _ = F' + t • (G - F') := by rw [smul_sub]
  constructor
  · -- Left disk
    have h_F'_in_left : F' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (F' - (-1) : ℂ) = F' + 1 by ring]
      exact hF'.1
    have h_G_in_left : G ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (G - (-1) : ℂ) = G + 1 by ring]
      exact hG.1
    have h_convex : Convex ℝ (Metric.closedBall ((-1) : ℂ) r_crit) :=
      convex_closedBall ((-1) : ℂ) r_crit
    have h_segment_subset : segment ℝ F' G ⊆ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_convex.segment_subset h_F'_in_left h_G_in_left
    have hp_in_left : p ∈ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_left
    simp only [dist_eq_norm] at hp_in_left
    rw [show (p - (-1) : ℂ) = p + 1 by ring] at hp_in_left
    exact hp_in_left
  · -- Right disk
    have h_F'_in_right : F' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hF'.2
    have h_G_in_right : G ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hG.2
    have h_convex : Convex ℝ (Metric.closedBall (1 : ℂ) r_crit) :=
      convex_closedBall (1 : ℂ) r_crit
    have h_segment_subset : segment ℝ F' G ⊆ Metric.closedBall (1 : ℂ) r_crit :=
      h_convex.segment_subset h_F'_in_right h_G_in_right
    have hp_in_right : p ∈ Metric.closedBall (1 : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_right
    simp only [dist_eq_norm] at hp_in_right
    exact hp_in_right

/--
G' lies in the disk intersection.
-/
lemma G'_in_disk_intersection : ‖G' + 1‖ ≤ r_crit ∧ ‖G' - 1‖ ≤ r_crit := by
  unfold G'
  have hG := G_on_segment_E'E
  obtain ⟨t, ht0, ht1, hG_eq⟩ := hG
  -- G = E' + t•(E - E'), so -G = -(E' + t•(E - E'))
  -- Since the disk intersection is symmetric about the origin
  -- (both disk centers ±1 are symmetric), -G is also in the intersection
  constructor
  · -- Show ‖-G + 1‖ ≤ r_crit
    rw [show (-G : ℂ) + 1 = -(G - 1) by ring, norm_neg]
    -- G is in the right disk, so ‖G - 1‖ ≤ r_crit
    rw [hG_eq]
    have : ‖E' + t • (E - E') - 1‖ ≤ r_crit :=
      (segment_in_disk_intersection t ⟨ht0, ht1⟩).2
    exact this
  · -- Show ‖-G - 1‖ ≤ r_crit
    rw [show (-G : ℂ) - 1 = -(G + 1) by ring, norm_neg]
    -- G is in the left disk, so ‖G + 1‖ ≤ r_crit
    rw [hG_eq]
    have : ‖E' + t • (E - E') + 1‖ ≤ r_crit :=
      (segment_in_disk_intersection t ⟨ht0, ht1⟩).1
    exact this

/--
Points on segment [F', G'] lie in the disk intersection.
-/
lemma segment_F'G'_in_intersection (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let p := F' + t • (G' - F')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  -- Both F' and G' lie in the disk intersection
  -- The disk intersection is convex, so the segment [F', G'] is also in it
  have hF' := F'_in_disk_intersection
  have hG' := G'_in_disk_intersection
  -- Use convexity of closed balls
  have hp_segment : p ∈ segment ℝ F' G' := by
    use (1 - t), t
    constructor; · linarith [ht0]
    constructor; · exact ht0
    constructor; · linarith [ht1]
    calc (1 - t) • F' + t • G'
        = F' - t • F' + t • G' := by rw [sub_smul, one_smul]
      _ = F' + (t • G' - t • F') := by ring
      _ = F' + t • (G' - F') := by rw [smul_sub]
  constructor
  · -- Left disk
    have h_F'_in_left : F' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (F' - (-1) : ℂ) = F' + 1 by ring]
      exact hF'.1
    have h_G'_in_left : G' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (G' - (-1) : ℂ) = G' + 1 by ring]
      exact hG'.1
    have h_convex : Convex ℝ (Metric.closedBall ((-1) : ℂ) r_crit) :=
      convex_closedBall ((-1) : ℂ) r_crit
    have h_segment_subset : segment ℝ F' G' ⊆ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_convex.segment_subset h_F'_in_left h_G'_in_left
    have hp_in_left : p ∈ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_left
    simp only [dist_eq_norm] at hp_in_left
    rw [show (p - (-1) : ℂ) = p + 1 by ring] at hp_in_left
    exact hp_in_left
  · -- Right disk
    have h_F'_in_right : F' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hF'.2
    have h_G'_in_right : G' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hG'.2
    have h_convex : Convex ℝ (Metric.closedBall (1 : ℂ) r_crit) :=
      convex_closedBall (1 : ℂ) r_crit
    have h_segment_subset : segment ℝ F' G' ⊆ Metric.closedBall (1 : ℂ) r_crit :=
      h_convex.segment_subset h_F'_in_right h_G'_in_right
    have hp_in_right : p ∈ Metric.closedBall (1 : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_right
    simp only [dist_eq_norm] at hp_in_right
    exact hp_in_right

/--
Points on segment [G', E] lie in the disk intersection.
-/
lemma segment_G'E_in_intersection (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let p := G' + t • (E - G')
    ‖p + 1‖ ≤ r_crit ∧ ‖p - 1‖ ≤ r_crit := by
  intro p
  -- Both G' and E lie in the disk intersection
  -- The disk intersection is convex, so the segment [G', E] is also in it
  have hG' := G'_in_disk_intersection
  have hE_left : ‖E + 1‖ ≤ r_crit := E_on_left_disk_boundary.le
  have hE_right : ‖E - 1‖ ≤ r_crit := E_in_right_disk
  -- Use convexity of closed balls
  have hp_segment : p ∈ segment ℝ G' E := by
    use (1 - t), t
    constructor; · linarith [ht0]
    constructor; · exact ht0
    constructor; · linarith [ht1]
    calc (1 - t) • G' + t • E
        = G' - t • G' + t • E := by rw [sub_smul, one_smul]
      _ = G' + (t • E - t • G') := by ring
      _ = G' + t • (E - G') := by rw [smul_sub]
  constructor
  · -- Left disk
    have h_G'_in_left : G' ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (G' - (-1) : ℂ) = G' + 1 by ring]
      exact hG'.1
    have h_E_in_left : E ∈ Metric.closedBall ((-1) : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      rw [show (E - (-1) : ℂ) = E + 1 by ring]
      exact hE_left
    have h_convex : Convex ℝ (Metric.closedBall ((-1) : ℂ) r_crit) :=
      convex_closedBall ((-1) : ℂ) r_crit
    have h_segment_subset : segment ℝ G' E ⊆ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_convex.segment_subset h_G'_in_left h_E_in_left
    have hp_in_left : p ∈ Metric.closedBall ((-1) : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_left
    simp only [dist_eq_norm] at hp_in_left
    rw [show (p - (-1) : ℂ) = p + 1 by ring] at hp_in_left
    exact hp_in_left
  · -- Right disk
    have h_G'_in_right : G' ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hG'.2
    have h_E_in_right : E ∈ Metric.closedBall (1 : ℂ) r_crit := by
      rw [Metric.mem_closedBall]; simp only [dist_eq_norm]
      exact hE_right
    have h_convex : Convex ℝ (Metric.closedBall (1 : ℂ) r_crit) :=
      convex_closedBall (1 : ℂ) r_crit
    have h_segment_subset : segment ℝ G' E ⊆ Metric.closedBall (1 : ℂ) r_crit :=
      h_convex.segment_subset h_G'_in_right h_E_in_right
    have hp_in_right : p ∈ Metric.closedBall (1 : ℂ) r_crit :=
      h_segment_subset hp_segment
    rw [Metric.mem_closedBall] at hp_in_right
    simp only [dist_eq_norm] at hp_in_right
    exact hp_in_right

/-! ## map1: Transformation E'F' → GF

The transformation map1 = genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv ∘ genA_inv
implements the first piece of the interval exchange on segment [E', E].
-/

/-! ### map1 Endpoint Proofs -/

/--
map1 sends endpoint E' to G.

To prove this, we need to compute:
map1 E' = genB_inv (genA_inv (genB_inv (genA_inv (genA_inv E'))))

This requires:
1. Expanding E' = -(ζ₅ - ζ₅²) = ζ₅² - ζ₅
2. Computing genA_inv E' = (E' + 1) * ζ₅⁻¹ - 1 (since E' is in left disk)
3. Iterating through each generator in the composition
4. Using ζ₅⁵ = 1 and ζ₅⁻¹ = ζ₅⁴ to simplify
5. Showing the result equals G = 2F - E
-/
lemma map1_endpoint_E' : map1 E' = G := by
  -- Strategy: Compute map1 E' step by step through the composition
  -- map1 = genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv ∘ genA_inv
  unfold map1 E' G F
  simp only [Function.comp_apply]
  -- First, we need to show E' is in both disks to use the generators
  have hE'_left : ‖E' + 1‖ ≤ r_crit := by
    convert E'_in_left_disk using 2
    ring
  have hE'_right : ‖E' - 1‖ ≤ r_crit := E'_on_right_disk_boundary.le
  -- This is a computational proof that requires expanding all the definitions
  -- and simplifying using cyclotomic identities
  sorry

/--
map1 sends endpoint F' to F.

This follows from pentagonal symmetry properties at the critical radius.
The transformation a⁻²b⁻¹a⁻¹b⁻¹ maps F' = -F to F through the five-fold rotation
composition.
-/
lemma map1_endpoint_F' : map1 F' = F := by
  -- Computational proof: track F' through map1 = genB_inv ∘ genA_inv ∘ genB_inv ∘ genA_inv ∘ genA_inv
  unfold map1
  simp only [Function.comp_apply]

  -- Establish disk membership facts we'll need
  have hF' : ‖F' + 1‖ ≤ r_crit ∧ ‖F' - 1‖ ≤ r_crit := by
    constructor
    · -- Show ‖F' + 1‖ ≤ r_crit
      sorry -- Will be proven by F'_in_disk_intersection lemma
    · -- Show ‖F' - 1‖ ≤ r_crit
      sorry -- Will be proven by F'_in_disk_intersection lemma

  -- Define intermediate points for clarity
  let z1 := genA_inv F'
  let z2 := genA_inv z1
  let z3 := genB_inv z2
  let z4 := genA_inv z3
  let z5 := genB_inv z4

  -- Show the final result equals F
  show z5 = F

  -- Step 1: Compute z1 = genA_inv F'
  have hz1 : z1 = (F' + 1) * ζ₅⁻¹ - 1 := by
    unfold z1 genA_inv
    simp [if_pos hF'.1]

  -- Step 1b: Show z1 is in left disk
  have hz1_left : ‖z1 + 1‖ ≤ r_crit := by
    rw [hz1]
    have : (F' + 1) * ζ₅⁻¹ - 1 + 1 = (F' + 1) * ζ₅⁻¹ := by ring
    rw [this, norm_mul, norm_inv, zeta5_abs, inv_one, mul_one]
    exact hF'.1

  -- Step 2: Compute z2 = genA_inv z1
  have hz2 : z2 = (z1 + 1) * ζ₅⁻¹ - 1 := by
    unfold z2 genA_inv
    simp [if_pos hz1_left]

  -- Step 2b: Show z2 is in both disks
  have hz2_left : ‖z2 + 1‖ ≤ r_crit := by
    rw [hz2]
    have : (z1 + 1) * ζ₅⁻¹ - 1 + 1 = (z1 + 1) * ζ₅⁻¹ := by ring
    rw [this, norm_mul, norm_inv, zeta5_abs, inv_one, mul_one]
    exact hz1_left

  have hz2_right : ‖z2 - 1‖ ≤ r_crit := by
    sorry -- Disk preservation from genA_inv

  -- Step 3: Compute z3 = genB_inv z2
  have hz3 : z3 = (z2 - 1) * ζ₅⁻¹ + 1 := by
    unfold z3 genB_inv
    simp [if_pos hz2_right]

  -- Step 3b: Show z3 is in left disk
  have hz3_left : ‖z3 + 1‖ ≤ r_crit :=
    genB_inv_preserves_left_disk_at_critical z2 hz2_left hz2_right

  have hz3_right : ‖z3 - 1‖ ≤ r_crit := by
    rw [hz3]
    have : (z2 - 1) * ζ₅⁻¹ + 1 - 1 = (z2 - 1) * ζ₅⁻¹ := by ring
    rw [this, norm_mul, norm_inv, zeta5_abs, inv_one, mul_one]
    exact hz2_right

  -- Step 4: Compute z4 = genA_inv z3
  have hz4 : z4 = (z3 + 1) * ζ₅⁻¹ - 1 := by
    unfold z4 genA_inv
    simp [if_pos hz3_left]

  -- Step 4b: Show z4 is in right disk
  have hz4_left : ‖z4 + 1‖ ≤ r_crit := by
    rw [hz4]
    have : (z3 + 1) * ζ₅⁻¹ - 1 + 1 = (z3 + 1) * ζ₅⁻¹ := by ring
    rw [this, norm_mul, norm_inv, zeta5_abs, inv_one, mul_one]
    exact hz3_left

  have hz4_right : ‖z4 - 1‖ ≤ r_crit :=
    genA_inv_preserves_right_disk_at_critical z3 hz3_left hz3_right

  -- Step 5: Compute z5 = genB_inv z4
  have hz5 : z5 = (z4 - 1) * ζ₅⁻¹ + 1 := by
    unfold z5 genB_inv
    simp [if_pos hz4_right]

  -- The algebraic expansion would show z5 = F, but this requires extensive
  -- cyclotomic computation with ζ₅. Mark as sorry for now.
  sorry

/-! ### map1 Bijection -/

/--
Transformation map1 establishes bijection between segments E'F' and GF.

The proof strategy is:
1. Show that map1 sends E' to G (requires symbolic computation with ζ₅)
2. Show that map1 sends F' to F (requires symbolic computation with ζ₅)
3. Use isometry property to conclude intermediate points map correctly
4. Parametrize the image to find s for each t

The main computational difficulty is verifying the endpoint mappings.
-/
theorem map1_bijection_E'F'_to_GF :
    ∃ (f : ℂ → ℂ), (∀ z, f z = map1 z) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      f (E' + t • (F' - E')) = G + s • (F - G)) := by
  use map1
  constructor
  · intro z; rfl
  · intro t ht0 ht1
    -- The proof requires:
    -- 1. Computing map1(E') and showing it equals G
    -- 2. Computing map1(F') and showing it equals F
    -- 3. Using the isometry property on [E', F'] (proven in
    --    maps_are_isometries_on_intersection)
    -- 4. Finding the parameter s such that map1(E' + t•(F' - E')) = G + s•(F - G)
    --
    -- The segments [E', F'] and [G, F] both lie in the disk intersection
    -- by segment_E'F'_in_intersection and segment_GF_in_intersection.
    --
    -- Key missing lemmas:
    -- - map1_endpoint_E' : map1 E' = G
    -- - map1_endpoint_F' : map1 F' = F
    --
    -- These require extensive computation with the 5th root of unity ζ₅.
    --
    -- PROOF OUTLINE (once endpoint lemmas are proven):
    -- Let p = E' + t•(F' - E'). We need to show ∃ s, map1 p = G + s•(F - G).
    --
    -- Step 1: Distance on source segment
    --   By properties of parameterized segments:
    --   dist(E', p) = t * dist(E', F')
    --   dist(p, F') = (1-t) * dist(E', F')
    --
    -- Step 2: Apply isometry
    --   By maps_are_isometries_on_intersection:
    --   dist(map1 E', map1 p) = dist(E', p) = t * dist(E', F')
    --   dist(map1 p, map1 F') = dist(p, F') = (1-t) * dist(E', F')
    --
    -- Step 3: Use endpoint mappings
    --   map1 E' = G (by map1_endpoint_E')
    --   map1 F' = F (by map1_endpoint_F')
    --   Therefore:
    --   dist(G, map1 p) = t * dist(E', F')
    --   dist(map1 p, F) = (1-t) * dist(E', F')
    --
    -- Step 4: Relate to target segment
    --   By isometry on endpoints:
    --   dist(G, F) = dist(map1 E', map1 F') = dist(E', F')
    --   Therefore:
    --   dist(G, map1 p) = t * dist(G, F)
    --   dist(map1 p, F) = (1-t) * dist(G, F)
    --
    -- Step 5: Deduce map1 p lies on [G, F]
    --   dist(G, map1 p) + dist(map1 p, F) = dist(G, F)
    --   By dist_add_dist_eq_iff (ℂ is strictly convex):
    --   map1 p ∈ segment [G, F]
    --   Since distances match parameterization: s = t
    sorry

/-! ## map2: Transformation F'G → FE

The transformation map2 = genB ∘ genB ∘ genA ∘ genB ∘ genA
implements the second piece of the interval exchange on segment [E', E].
-/

/-! ### map2 Endpoint Proofs -/

/--
map2 sends F' to F (endpoint mapping).
-/
lemma map2_sends_F'_to_F : map2 F' = F := by
  -- This requires computing map2(-F) = (b∘b∘a∘b∘a)(-F)
  -- through all five rotation compositions.
  -- The calculation involves:
  -- 1. Expressing F in terms of ζ₅ using F = 1 - ζ₅ + ζ₅² - ζ₅³
  -- 2. Tracking -F through each rotation by ±2π/5
  -- 3. Verifying the final result equals F
  --
  -- This is a substantial symbolic computation requiring:
  -- - Expansion of -F = -(1 - ζ₅ + ζ₅² - ζ₅³)
  -- - Applying each rotation in sequence
  -- - Using pentagonal symmetry properties
  -- - Simplifying using ζ₅⁵ = 1 and cyclotomic identities
  sorry

/--
map2 sends G' to E (endpoint mapping).
-/
lemma map2_sends_G'_to_E : map2 G' = E := by
  -- This requires computing map2(G') = map2(-G) = (b∘b∘a∘b∘a)(-G)
  -- through all five rotation compositions.
  -- Similar to map2_sends_F'_to_F, this involves:
  -- 1. Expressing G' = -G = -(2F - E) in terms of ζ₅
  -- 2. Tracking G' through each rotation by ±2π/5
  -- 3. Verifying the final result equals E = ζ₅ - ζ₅²
  --
  -- The pentagonal symmetry at the critical radius r_crit = √(3 + φ)
  -- ensures this mapping works correctly, but proving it requires
  -- extensive calculation with complex numbers and trigonometry.
  sorry

/-! ### map2 Bijection -/

/--
Transformation map2 establishes bijection between segments F'G' and FE.

The proof strategy:
1. F' is defined as -F (reflection through origin, like E' = -E)
2. G' is defined as -G (reflection through origin)
3. map2 is an isometry on the disk intersection (proven in maps_are_isometries_on_intersection)
4. map2(F') = F and map2(G') = E (computational lemmas map2_sends_F'_to_F and map2_sends_G'_to_E)
5. Therefore map2 maps segment [F', G'] to segment [F, E] preserving parametrization

The computational difficulty is in the endpoint mapping lemmas (marked as sorry),
which require extensive symbolic computation with ζ₅.
-/
theorem map2_bijection_FpG_to_FE :
    ∃ (f : ℂ → ℂ) (F' : ℂ), (∀ z, f z = map2 z) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      f (F' + t • (G' - F')) = F + s • (E - F)) := by
  -- Define F' as the reflection of F through the origin
  -- This follows the pentagonal symmetry pattern: F' = -F
  use map2, F'
  constructor
  · -- Show f = map2
    intro z; rfl
  · intro t ht0 ht1
    -- We choose s = t
    -- The key insight is that isometries preserve line segment parametrization
    use t
    constructor
    · exact ht0
    constructor
    · exact ht1
    · -- Show: map2 (F' + t • (G' - F')) = F + t • (E - F)
      --
      -- Strategy:
      -- map2 is an isometry on the disk intersection, so it maps line segments
      -- to line segments while preserving the parameter.
      --
      -- We have (by the computational lemmas):
      --   map2(F') = F          (by map2_sends_F'_to_F)
      --   map2(G') = E          (by map2_sends_G'_to_E)
      --
      -- For an isometry mapping a segment [A, B] to [C, D], we have:
      --   map(A + t•(B - A)) = C + t•(D - C)
      -- when map(A) = C and map(B) = D.
      --
      -- Therefore:
      --   map2(F' + t•(G' - F')) = map2(F') + t•(map2(G') - map2(F'))
      --                          = F + t•(E - F)
      --
      -- This requires proving a general lemma about isometries on segments,
      -- which is currently marked as sorry.
      sorry

/-! ## map3: Transformation G'E → E'G

The transformation map3 = genB_inv ∘ genA_inv ∘ genB_inv ∘ genA ∘ genB ∘ genA
implements the third piece of the interval exchange on segment [E', E].
-/

/-! ### map3 Endpoint Proofs -/

/--
map3 sends G' to E' (endpoint mapping).
-/
lemma map3_sends_G'_to_E' : map3 G' = E' := by
  -- This requires computing map3(-G) = (b⁻¹∘a⁻¹∘b⁻¹∘a∘b∘a)(-G)
  -- through all six rotation compositions.
  -- The calculation involves:
  -- 1. Expressing G in terms of ζ₅ using G = 2F - E
  -- 2. Tracking -G through each rotation by ±2π/5
  -- 3. Verifying the final result equals E' = -E
  --
  -- This is a substantial symbolic computation requiring:
  -- - Expansion of G = 2F - E = 2(1 - ζ₅ + ζ₅² - ζ₅³) - (ζ₅ - ζ₅²)
  -- - Applying each rotation in sequence
  -- - Using pentagonal symmetry properties
  -- - Simplifying using ζ₅⁵ = 1 and cyclotomic identities
  sorry

/--
map3 sends E to G (endpoint mapping).
-/
lemma map3_sends_E_to_G : map3 E = G := by
  -- This requires computing map3(E) = (b⁻¹∘a⁻¹∘b⁻¹∘a∘b∘a)(E)
  -- through all six rotation compositions.
  -- Similar to map3_sends_G'_to_E', this involves:
  -- 1. Expressing E = ζ₅ - ζ₅²
  -- 2. Tracking E through each rotation by ±2π/5
  -- 3. Verifying the final result equals G = 2F - E
  --
  -- The pentagonal symmetry at the critical radius r_crit = √(3 + φ)
  -- ensures this mapping works correctly, but proving it requires
  -- extensive calculation with complex numbers and trigonometry.
  sorry

/-! ### map3 Bijection -/

/--
Transformation map3 establishes bijection between segments G'E and E'G.

The proof strategy is:
1. Define G' as the image of G under appropriate transformations
2. Show that map3 sends G' to E' and E to G
3. Use isometry property on [G', E]
4. Parametrize the image to find s for each t

Like map1 and map2, the main computational difficulty is verifying the endpoint
mappings, which requires extensive symbolic computation with ζ₅.
-/
theorem map3_bijection_GpE_to_E'G :
    ∃ (f : ℂ → ℂ) (G' : ℂ), (∀ z, f z = map3 z) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      f (G' + t • (E - G')) = E' + s • (G - E')) := by
  -- Define G' as the reflection of G through the origin
  -- This follows the pentagonal symmetry: G' = -G
  use map3, G'
  constructor
  · -- Show f = map3
    intro z; rfl
  · intro t ht0 ht1
    -- Proof outline:
    -- Step 1: Verify segment [G', E] lies in disk intersection (proven)
    -- Step 2: Use endpoint mappings map3(G') = E' and map3(E) = G (sorries)
    -- Step 3: Apply isometry property of map3
    -- Step 4: Construct parameter s for the bijection

    -- The point G' + t•(E - G') is in the disk intersection
    have hp_in_intersection := segment_G'E_in_intersection t ht0 ht1

    -- Consider the image under map3
    let p := G' + t • (E - G')
    let q := map3 p

    -- By the endpoint mappings (which are computational sorries):
    -- - map3(G') = E' (when t = 0)
    -- - map3(E) = G (when t = 1)
    --
    -- By the isometry property (proven in maps_are_isometries_on_intersection):
    -- - ‖map3(z) - map3(w)‖ = ‖z - w‖ for all z, w in the intersection
    --
    -- This means map3 maps the segment [G', E] isometrically to some segment.
    -- Since the endpoints map to E' and G respectively, the image must be
    -- a segment from E' to G.
    --
    -- To find the parameter s, we would need to solve:
    --   map3(G' + t•(E - G')) = E' + s•(G - E')
    --
    -- The isometry property ensures this equation has a unique solution s ∈ [0,1].
    -- Computing s explicitly requires the endpoint mappings and the isometry formula.

    -- The main obstacles are:
    -- 1. Computing map3(G') = E' explicitly (marked sorry in map3_sends_G'_to_E')
    -- 2. Computing map3(E) = G explicitly (marked sorry in map3_sends_E_to_G)
    -- 3. Using these to derive the formula for the parameter s
    --
    -- All three require extensive symbolic computation with ζ₅ through
    -- 6 compositions of rotations by ±2π/5, which is beyond current
    -- algebraic automation capabilities in Lean.
    sorry

end TDCSG.CompoundSymmetry.GG5
