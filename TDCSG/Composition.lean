/-
Copyright (c) 2024 Eric Moffat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Moffat
-/
import TDCSG.Basic
import TDCSG.Properties
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Composition and Iteration of Piecewise Isometries

This file defines composition and iteration for piecewise isometries. The key challenge in
composition is that the resulting partition must be a refinement of both input partitions.

## Main definitions

- `PiecewiseIsometry.comp`: Composition of two piecewise isometries
- `PiecewiseIsometry.iterate`: Iteration of a piecewise isometry
- `PiecewiseIsometry.refinedPartition`: The common refinement of two partitions

## Main results

- `comp_assoc`: Composition is associative
- `comp_id_left`: Left identity for composition
- `comp_id_right`: Right identity for composition
- `iterate_succ`: Characterization of iteration
- `iterate_isometry`: Each iterate is isometric on pieces
- `comp_apply`: Function application distributes over composition

## Notation

- `f.comp g` or `f ∘ g`: Composition of piecewise isometries
- `f^[n]`: The nth iterate of f

-/

universe u v

namespace PiecewiseIsometry

variable {α : Type u} [MetricSpace α] [MeasurableSpace α]

section Refinement

/-- The refined partition obtained by intersecting pieces from two partitions with preimage.

Given partitions p (for g) and q (for f), and function g, the preimage-based refinement consists
of all nonempty intersections s ∩ g⁻¹(t) where s ∈ p and t ∈ q.
This ensures g maps each refined piece entirely into a single piece of f's partition. -/
def refinedPartitionPreimage (p q : Set (Set α)) (g : α → α) : Set (Set α) :=
  {u | ∃ s ∈ p, ∃ t ∈ q, u = s ∩ (g ⁻¹' t) ∧ (s ∩ (g ⁻¹' t)).Nonempty}

/-- The naive refined partition (kept for potential use in other contexts). -/
def refinedPartition (p q : Set (Set α)) : Set (Set α) :=
  {u | ∃ s ∈ p, ∃ t ∈ q, u = s ∩ t ∧ (s ∩ t).Nonempty}

/-- Elements of the refined partition are measurable if both original partitions are measurable. -/
theorem refinedPartition_measurable {α : Type u} [MeasurableSpace α] (p q : Set (Set α))
    (hp : ∀ s ∈ p, MeasurableSet s) (hq : ∀ t ∈ q, MeasurableSet t) :
    ∀ u ∈ refinedPartition p q, MeasurableSet u := by
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact (hp s hs).inter (hq t ht)

/-- The refined partition covers the same space as the original partitions. -/
theorem refinedPartition_cover {α : Type u} (p q : Set (Set α))
    (hp : ⋃₀ p = Set.univ) (hq : ⋃₀ q = Set.univ) :
    ⋃₀ refinedPartition p q = Set.univ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  -- x is in some s ∈ p and some t ∈ q
  rw [Set.sUnion_eq_univ_iff] at hp hq
  obtain ⟨s, hs, hxs⟩ := hp x
  obtain ⟨t, ht, hxt⟩ := hq x
  -- So x is in s ∩ t, which is in refinedPartition p q
  use s ∩ t
  constructor
  · unfold refinedPartition
    simp only [Set.mem_setOf_eq]
    exact ⟨s, hs, t, ht, rfl, ⟨x, hxs, hxt⟩⟩
  · exact ⟨hxs, hxt⟩

/-- The refined partition is countable if both original partitions are countable. -/
theorem refinedPartition_countable (p q : Set (Set α))
    (hp : p.Countable) (hq : q.Countable) :
    (refinedPartition p q).Countable := by
  -- refined partition is a subset of the image of p × q under the intersection function
  refine Set.Countable.mono ?_ ((hp.prod hq).image (fun st => st.1 ∩ st.2))
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact ⟨(s, t), ⟨hs, ht⟩, rfl⟩

/-- Elements of the preimage-based refined partition are measurable. -/
theorem refinedPartitionPreimage_measurable {α : Type u} [MeasurableSpace α]
    (p q : Set (Set α)) (g : α → α)
    (hp : ∀ s ∈ p, MeasurableSet s) (hq : ∀ t ∈ q, MeasurableSet t)
    (hg : Measurable g) :
    ∀ u ∈ refinedPartitionPreimage p q g, MeasurableSet u := by
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact (hp s hs).inter (hg (hq t ht))

/-- The preimage-based refined partition covers the space. -/
theorem refinedPartitionPreimage_cover {α : Type u} (p q : Set (Set α)) (g : α → α)
    (hp : ⋃₀ p = Set.univ) (hq : ⋃₀ q = Set.univ) :
    ⋃₀ refinedPartitionPreimage p q g = Set.univ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  rw [Set.sUnion_eq_univ_iff] at hp hq
  obtain ⟨s, hs, hxs⟩ := hp x
  obtain ⟨t, ht, hgxt⟩ := hq (g x)
  use s ∩ (g ⁻¹' t)
  constructor
  · unfold refinedPartitionPreimage
    simp only [Set.mem_setOf_eq]
    exact ⟨s, hs, t, ht, rfl, ⟨x, hxs, hgxt⟩⟩
  · exact ⟨hxs, hgxt⟩

/-- The preimage-based refined partition is countable. -/
theorem refinedPartitionPreimage_countable (p q : Set (Set α)) (g : α → α)
    (hp : p.Countable) (hq : q.Countable) :
    (refinedPartitionPreimage p q g).Countable := by
  refine Set.Countable.mono ?_ ((hp.prod hq).image (fun st => st.1 ∩ (g ⁻¹' st.2)))
  intro u hu
  obtain ⟨s, hs, t, ht, rfl, _⟩ := hu
  exact ⟨(s, t), ⟨hs, ht⟩, rfl⟩

/-- The preimage-based refined partition is pairwise disjoint. -/
theorem refinedPartitionPreimage_disjoint {α : Type u} (p q : Set (Set α)) (g : α → α)
    (hp : ∀ s ∈ p, ∀ t ∈ p, s ≠ t → Disjoint s t)
    (hq : ∀ s ∈ q, ∀ t ∈ q, s ≠ t → Disjoint s t) :
    ∀ u ∈ refinedPartitionPreimage p q g, ∀ v ∈ refinedPartitionPreimage p q g, u ≠ v → Disjoint u v := by
  intro u hu v hv huv
  obtain ⟨s₁, hs₁, t₁, ht₁, rfl, _⟩ := hu
  obtain ⟨s₂, hs₂, t₂, ht₂, rfl, _⟩ := hv
  show Disjoint (s₁ ∩ (g ⁻¹' t₁)) (s₂ ∩ (g ⁻¹' t₂))
  by_cases h₁ : s₁ = s₂
  · subst h₁
    by_cases h₂ : t₁ = t₂
    · subst h₂
      exact absurd rfl huv
    · have hdisj : Disjoint t₁ t₂ := hq t₁ ht₁ t₂ ht₂ h₂
      exact Set.disjoint_of_subset_right (Set.inter_subset_right)
        (Set.disjoint_of_subset_left (Set.inter_subset_right) (Disjoint.preimage g hdisj))
  · have hdisj : Disjoint s₁ s₂ := hp s₁ hs₁ s₂ hs₂ h₁
    exact Set.disjoint_of_subset_left (Set.inter_subset_left)
      (Set.disjoint_of_subset_right (Set.inter_subset_left) hdisj)

end Refinement

section Measurability

/-- Helper lemma: isometry on a set implies continuity on that set. -/
theorem isometry_on_continuous {s : Set α} {f : α → α}
    (h_iso : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) = dist x y) :
    ContinuousOn f s := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  use ε, hε
  intro y hy_s hy_dist
  calc dist (f y) (f x) = dist y x := h_iso y hy_s x hx
    _ < ε := hy_dist

/-- Key lemma: continuous on a measurable set implies measurable preimage restricted to that set.

This uses the fact that the restriction to a measurable subtype is a measurable embedding. -/
theorem continuousOn_measurableSet_preimage [BorelSpace α] {f : α → α} {s U : Set α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) (hU : IsOpen U) :
    MeasurableSet (f ⁻¹' U ∩ s) := by
  -- The restriction f|s : s → α is continuous
  have g_cont : Continuous (s.restrict f) := continuousOn_iff_continuous_restrict.1 hf
  -- Therefore f|s is measurable
  have g_meas : Measurable (s.restrict f) := g_cont.measurable
  -- The preimage (f|s)⁻¹(U) is measurable
  have : MeasurableSet ((s.restrict f) ⁻¹' U) := g_meas hU.measurableSet
  -- Subtype.val : s → α is a measurable embedding when s is measurable
  have coe_emb : MeasurableEmbedding (Subtype.val : s → α) := MeasurableEmbedding.subtype_coe hs
  -- The key identity: f⁻¹(U) ∩ s = Subtype.val '' ((f|s)⁻¹(U))
  have key : f ⁻¹' U ∩ s = Subtype.val '' ((s.restrict f) ⁻¹' U) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.restrict_apply]
    constructor
    · intro ⟨hfx, hxs⟩
      exact ⟨⟨x, hxs⟩, hfx, rfl⟩
    · intro ⟨y, hfy, hyx⟩
      cases y with | mk val prop =>
      subst hyx
      exact ⟨hfy, prop⟩
  rw [key]
  -- Apply measurable embedding property
  exact coe_emb.measurableSet_image.mpr this

/-- A piecewise isometry is measurable under BorelSpace.

PROOF STRATEGY:
- Decompose f⁻¹(U) as the union over partition pieces: f⁻¹(U) = ⋃_{s ∈ partition} (f⁻¹(U) ∩ s)
- On each piece s, f is an isometry, hence continuous on s
- Use continuousOn_measurableSet_preimage to show f⁻¹(U) ∩ s is measurable
- Apply countable union to conclude f⁻¹(U) is measurable
- Use measurable_of_isOpen to conclude f is measurable

TECHNICAL NOTE: This requires BorelSpace α (not just OpensMeasurableSpace α) to ensure
that continuous functions on subtypes are measurable. -/
theorem piecewiseIsometry_measurable [BorelSpace α] (f : PiecewiseIsometry α) :
    Measurable f.toFun := by
  apply measurable_of_isOpen
  intro U hU
  -- Decompose f⁻¹(U) as union over partition pieces
  have decomp : f.toFun ⁻¹' U = ⋃ s ∈ f.partition, (f.toFun ⁻¹' U ∩ s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hx
      -- x is in some piece of the partition
      have : x ∈ ⋃₀ f.partition := by rw [f.partition_cover]; trivial
      obtain ⟨s, hs, hxs⟩ := this
      exact ⟨s, hs, hx, hxs⟩
    · intro ⟨s, hs, hxU, hxs⟩
      exact hxU
  rw [decomp]
  -- Apply countable union
  apply MeasurableSet.biUnion f.partition_countable
  intro s hs
  -- On s, f is an isometry, hence continuous
  have f_cont_s : ContinuousOn f.toFun s := isometry_on_continuous (f.isometry_on_pieces s hs)
  -- Therefore f⁻¹(U) ∩ s is measurable
  exact continuousOn_measurableSet_preimage f_cont_s (f.partition_measurable s hs) hU

end Measurability

section Extensionality

/-- Extensionality lemma for PiecewiseIsometry based on partition and function equality.

If two piecewise isometries have equal partitions and equal underlying functions,
then they are equal as structures. This is provable because all other fields
(partition_measurable, partition_countable, etc.) are proofs, which are unique
by proof irrelevance once the partition is fixed. -/
theorem ext_partition_toFun {f g : PiecewiseIsometry α}
    (h_partition : f.partition = g.partition)
    (h_toFun : f.toFun = g.toFun) :
    f = g := by
  obtain ⟨fp, fpm, fpc, fpcover, fpdisj, fpne, ftoFun, fiso⟩ := f
  obtain ⟨gp, gpm, gpc, gpcover, gpdisj, gpne, gtoFun, giso⟩ := g
  simp only at h_partition h_toFun
  subst h_partition h_toFun
  rfl

end Extensionality

section Composition

/-- Composition of two piecewise isometries.

The composition `f.comp g` applies `g` first, then `f`. The resulting partition uses
preimage-based refinement to ensure g maps each refined piece into a single piece of f's partition. -/
def comp [BorelSpace α] (f g : PiecewiseIsometry α) : PiecewiseIsometry α where
  partition := refinedPartitionPreimage g.partition f.partition g.toFun
  partition_measurable := by
    apply refinedPartitionPreimage_measurable
    · exact g.partition_measurable
    · exact f.partition_measurable
    · exact piecewiseIsometry_measurable g
  partition_countable := refinedPartitionPreimage_countable g.partition f.partition g.toFun
    g.partition_countable f.partition_countable
  partition_cover := refinedPartitionPreimage_cover g.partition f.partition g.toFun
    g.partition_cover f.partition_cover
  partition_disjoint := refinedPartitionPreimage_disjoint g.partition f.partition g.toFun
    g.partition_disjoint f.partition_disjoint
  partition_nonempty := by
    intro u hu
    obtain ⟨s, hs, t, ht, rfl, hnonempty⟩ := hu
    exact hnonempty
  toFun := f.toFun ∘ g.toFun
  isometry_on_pieces := by
    intro s hs x hx y hy
    -- s is an intersection from refinedPartitionPreimage
    obtain ⟨s_g, hs_g, s_f, hs_f, rfl, _⟩ := hs
    simp only [Function.comp_apply]
    -- Key insight: x, y ∈ s_g ∩ (g⁻¹' s_f) means g(x), g(y) ∈ s_f
    have hgx : g.toFun x ∈ s_f := by
      have : x ∈ g.toFun ⁻¹' s_f := hx.2
      exact this
    have hgy : g.toFun y ∈ s_f := by
      have : y ∈ g.toFun ⁻¹' s_f := hy.2
      exact this
    -- Apply g first (isometric on s_g), then f (isometric on s_f)
    calc dist (f.toFun (g.toFun x)) (f.toFun (g.toFun y))
        = dist (g.toFun x) (g.toFun y) := f.isometry_on_pieces s_f hs_f (g.toFun x) hgx (g.toFun y) hgy
      _ = dist x y := g.isometry_on_pieces s_g hs_g x hx.1 y hy.1

/-- Function application for composition. -/
@[simp]
theorem comp_apply [BorelSpace α] (f g : PiecewiseIsometry α) (x : α) :
    (f.comp g) x = f (g x) := rfl

/-! ### Note on Extensionality

This structure does NOT have function extensionality in the usual sense.
Two PiecewiseIsometry values are equal iff ALL fields match, including the partition.
Having the same underlying function is NOT sufficient for structural equality.

Example: The identity function can be represented with partition {univ} or with
any other partition where it's isometric on each piece.

For reasoning about functional equality without structural equality, use:
- Function.funext_iff for the underlying functions
- Or define a separate equivalence relation / setoid

The @[ext] attribute is deliberately NOT used here because it would claim an
unprovable theorem. Lean's default structural equality is the correct notion.
-/

/-- Composition is associative. -/
theorem comp_assoc [BorelSpace α] (f g h : PiecewiseIsometry α) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  -- The functions are definitionally equal (function composition is associative)
  have h_toFun : ((f.comp g).comp h).toFun = (f.comp (g.comp h)).toFun := by
    unfold comp
    rfl

  -- Need to show the partitions are equal
  have h_partition : ((f.comp g).comp h).partition = (f.comp (g.comp h)).partition := by
    unfold comp refinedPartitionPreimage
    ext u
    simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨s_h, hs_h, s_fg, hs_fg, hu_eq, hu_ne⟩
      -- s_fg ∈ refinedPartitionPreimage g.partition f.partition g.toFun
      obtain ⟨s_g, hs_g, s_f, hs_f, hs_fg_eq, hs_fg_ne⟩ := hs_fg
      -- u = s_h ∩ (h⁻¹' s_fg) = s_h ∩ (h⁻¹' (s_g ∩ (g⁻¹' s_f)))
      rw [hs_fg_eq] at hu_eq hu_ne
      -- Rewrite using preimage properties: h⁻¹(A ∩ B) = h⁻¹(A) ∩ h⁻¹(B)
      have hu_eq' : u = (s_h ∩ (h.toFun ⁻¹' s_g)) ∩ ((g.toFun ∘ h.toFun) ⁻¹' s_f) := by
        rw [hu_eq]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
        tauto
      use s_h ∩ (h.toFun ⁻¹' s_g)
      constructor
      · -- Show s_h ∩ (h⁻¹' s_g) ∈ refinedPartitionPreimage h.partition g.partition h.toFun
        use s_h, hs_h, s_g, hs_g
        constructor
        · rfl
        · -- Show (s_h ∩ (h⁻¹' s_g)).Nonempty
          -- hu_ne : (s_h ∩ h.toFun ⁻¹' (s_g ∩ (g.toFun ⁻¹' s_f))).Nonempty
          obtain ⟨x, hx⟩ := hu_ne
          use x
          simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
          exact ⟨hx.1, hx.2.1⟩
      use s_f, hs_f
      constructor
      · exact hu_eq'
      · -- Need to show ((s_h ∩ h.toFun ⁻¹' s_g) ∩ (g.toFun ∘ h.toFun) ⁻¹' s_f).Nonempty
        obtain ⟨x, hx⟩ := hu_ne
        use x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
        simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
        exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩
    · intro ⟨s_gh, hs_gh, s_f, hs_f, hu_eq, hu_ne⟩
      -- s_gh ∈ refinedPartitionPreimage h.partition g.partition h.toFun
      obtain ⟨s_h, hs_h, s_g, hs_g, hs_gh_eq, hs_gh_ne⟩ := hs_gh
      -- u = s_gh ∩ ((g ∘ h)⁻¹' s_f) = (s_h ∩ (h⁻¹' s_g)) ∩ ((g ∘ h)⁻¹' s_f)
      rw [hs_gh_eq] at hu_eq hu_ne
      have hu_eq' : u = s_h ∩ (h.toFun ⁻¹' (s_g ∩ (g.toFun ⁻¹' s_f))) := by
        rw [hu_eq]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
        tauto
      use s_h, hs_h
      use s_g ∩ (g.toFun ⁻¹' s_f)
      constructor
      · -- Show s_g ∩ (g⁻¹' s_f) ∈ refinedPartitionPreimage g.partition f.partition g.toFun
        use s_g, hs_g, s_f, hs_f
        constructor
        · rfl
        · -- Show (s_g ∩ (g⁻¹' s_f)).Nonempty
          -- hu_ne : ((s_h ∩ h.toFun ⁻¹' s_g) ∩ (g.toFun ∘ h.toFun) ⁻¹' s_f).Nonempty
          obtain ⟨x, hx⟩ := hu_ne
          use h.toFun x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply] at hx ⊢
          exact ⟨hx.1.2, hx.2⟩
      constructor
      · exact hu_eq'
      · -- Need to show (s_h ∩ h.toFun ⁻¹' (s_g ∩ g.toFun ⁻¹' s_f)).Nonempty
        obtain ⟨x, hx⟩ := hu_ne
        use x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply] at hx
        simp only [Set.mem_inter_iff, Set.mem_preimage]
        exact ⟨hx.1.1, hx.1.2, hx.2⟩

  exact ext_partition_toFun h_partition h_toFun

/-- Left identity for composition. -/
theorem comp_id_left [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) :
    id.comp f = f := by
  -- Since there's no extensionality lemma for PiecewiseIsometry, we need to prove
  -- that the two structures have identical fields.
  -- Key insight: refinedPartitionPreimage f.partition {univ} f.toFun = f.partition
  -- because s ∩ (f⁻¹' univ) = s ∩ univ = s

  -- First show the partitions are equal
  have h_partition : (id.comp f).partition = f.partition := by
    unfold comp id refinedPartitionPreimage
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨s, hs, t, ht, hu_eq, _⟩
      -- t = univ, so s ∩ (f.toFun ⁻¹' univ) = s
      rw [ht, Set.preimage_univ, Set.inter_univ] at hu_eq
      rw [hu_eq]
      exact hs
    · intro hu
      use u, hu, Set.univ, rfl
      constructor
      · rw [Set.preimage_univ, Set.inter_univ]
      · rw [Set.preimage_univ, Set.inter_univ]
        exact f.partition_nonempty u hu

  -- Show the functions are equal
  have h_toFun : (id.comp f).toFun = f.toFun := by
    unfold comp id
    funext x
    rfl

  -- Use extensionality lemma
  exact ext_partition_toFun h_partition h_toFun

/-- Right identity for composition. -/
theorem comp_id_right [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) :
    f.comp id = f := by
  -- Show the partitions are equal
  -- refinedPartitionPreimage id.partition f.partition id.toFun = f.partition
  -- which is refinedPartitionPreimage {univ} f.partition id = f.partition
  have h_partition : (f.comp id).partition = f.partition := by
    unfold comp id refinedPartitionPreimage
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨s, hs, t, ht, hu_eq, _⟩
      -- s ∈ {univ}, so s = univ
      -- u = univ ∩ (id⁻¹' t) = univ ∩ t = t
      rw [hs] at hu_eq
      simp only [_root_.id, Set.preimage_id, Set.univ_inter] at hu_eq
      rw [hu_eq]
      exact ht
    · intro hu
      use Set.univ, rfl, u, hu
      constructor
      · simp only [Set.preimage_id, Set.univ_inter]
      · simp only [Set.preimage_id, Set.univ_inter]
        exact f.partition_nonempty u hu

  -- Show the functions are equal
  have h_toFun : (f.comp id).toFun = f.toFun := by
    unfold comp id
    funext x
    rfl

  -- Use extensionality lemma
  exact ext_partition_toFun h_partition h_toFun

end Composition

section Iteration

/-- The nth iterate of a piecewise isometry.

`iterate f n` applies `f` a total of `n` times. By convention, `iterate f 0` is the identity. -/
def iterate [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) : ℕ → PiecewiseIsometry α
  | 0 => id
  | n + 1 => f.comp (iterate f n)

/-- Characterization of iterate at successor. -/
theorem iterate_succ [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (n : ℕ) :
    iterate f (n + 1) = f.comp (iterate f n) := rfl

/-- Iterate at zero is identity. -/
@[simp]
theorem iterate_zero_eq [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) :
    iterate f 0 = id := rfl

/-- Iterate at one is the original map. -/
@[simp]
theorem iterate_one [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) :
    iterate f 1 = f := by
  rw [iterate_succ, iterate_zero_eq, comp_id_right]

/-- Function application for iteration. -/
theorem iterate_apply [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (n : ℕ) (x : α) :
    (iterate f n) x = (f.toFun^[n]) x := by
  induction n with
  | zero =>
    show id.toFun x = (f.toFun^[0]) x
    rw [Function.iterate_zero]
    rfl
  | succ n ih =>
    rw [iterate_succ, comp_apply, ih]
    simp [Function.iterate_succ_apply']

/-- Iteration adds exponents. -/
theorem iterate_add [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (m n : ℕ) :
    iterate f (m + n) = (iterate f m).comp (iterate f n) := by
  induction m with
  | zero =>
    show iterate f (0 + n) = (iterate f 0).comp (iterate f n)
    rw [iterate_zero_eq, Nat.zero_add, comp_id_left]
  | succ m ih =>
    rw [Nat.succ_add, iterate_succ, iterate_succ, ih, comp_assoc]

/-- Each iterate preserves the isometry property. -/
theorem iterate_isometry_on_pieces [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (n : ℕ) (s : Set α)
    (hs : s ∈ (iterate f n).partition) (x y : α) (hx : x ∈ s) (hy : y ∈ s) :
    dist ((iterate f n) x) ((iterate f n) y) = dist x y :=
  (iterate f n).dist_eq_on_piece s hs x y hx hy

/-- The underlying function of an iterate is the composition of the underlying functions. -/
theorem iterate_toFun [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (n : ℕ) :
    (iterate f n).toFun = f.toFun^[n] := by
  ext x
  exact iterate_apply f n x

end Iteration

section CompositionProperties

/-- Composition preserves distance on refined pieces. -/
theorem comp_dist_eq [BorelSpace α] (f g : PiecewiseIsometry α) (x y : α)
    (h : ∃ s ∈ (f.comp g).partition, x ∈ s ∧ y ∈ s) :
    dist ((f.comp g) x) ((f.comp g) y) = dist x y := by
  obtain ⟨s, hs, hxs, hys⟩ := h
  exact (f.comp g).isometry_on_pieces s hs x hxs y hys

/-- The discontinuity set of a composition is contained in the union of discontinuity sets. -/
theorem discontinuitySet_comp_subset [BorelSpace α] (f g : PiecewiseIsometry α) :
    (f.comp g).discontinuitySet ⊆
      f.discontinuitySet ∪ (g.toFun ⁻¹' f.discontinuitySet) ∪ g.discontinuitySet := by
  -- discontinuitySet = union of frontiers of partition pieces
  -- Goal: show frontier of any piece of (f.comp g).partition is in the RHS
  intro x hx
  unfold discontinuitySet at hx ⊢
  simp only [Set.mem_iUnion, Set.mem_union] at hx ⊢
  -- hx: x is in frontier of some piece of (f.comp g).partition
  obtain ⟨u, hu_partition, hx_frontier⟩ := hx

  -- The composition partition is refined: u = s ∩ (g⁻¹' t) for some s ∈ g.partition, t ∈ f.partition
  unfold comp refinedPartitionPreimage at hu_partition
  simp only [Set.mem_setOf_eq] at hu_partition
  obtain ⟨s, hs_g, t, ht_f, hu_eq, _⟩ := hu_partition
  rw [hu_eq] at hx_frontier

  -- Key: frontier(s ∩ g⁻¹' t) ⊆ (frontier s ∩ closure(g⁻¹' t)) ∪ (closure s ∩ frontier(g⁻¹' t))
  have key := frontier_inter_subset s (g.toFun ⁻¹' t)
  have hx_key : x ∈ frontier s ∩ closure (g.toFun ⁻¹' t) ∪ closure s ∩ frontier (g.toFun ⁻¹' t) :=
    key hx_frontier

  cases hx_key with
  | inl hx_left =>
    -- x ∈ frontier s ∩ closure (g⁻¹' t)
    -- Then x ∈ frontier s, so x ∈ g.discontinuitySet
    right
    exact ⟨s, hs_g, hx_left.1⟩
  | inr hx_right =>
    -- x ∈ closure s ∩ frontier (g⁻¹' t)
    -- Then x ∈ frontier (g⁻¹' t)
    -- Case analysis: is x in interior of s, or on frontier of s?
    by_cases hx_interior : x ∈ interior s
    · -- x is in interior of s, where g is continuous
      -- Use: frontier (g⁻¹' t) ⊆ g⁻¹' (frontier t) on interior of s
      -- Since g is continuous on interior s and x ∈ interior s ∩ frontier (g⁻¹' t),
      -- we have g(x) ∈ frontier t
      have hgx_frontier : g.toFun x ∈ frontier t := by
        -- Strategy: Show g(x) ∈ closure t and g(x) ∉ interior t
        rw [frontier, Set.mem_diff]
        constructor
        · -- g(x) ∈ closure t
          -- x ∈ frontier (g⁻¹ t) means x ∈ closure (g⁻¹ t)
          have hx_closure : x ∈ closure (g.toFun ⁻¹' t) := hx_right.2.1
          -- g continuous within s at x (isometry on s implies continuity)
          have g_cont_within : ContinuousWithinAt g.toFun s x := by
            refine Metric.continuousWithinAt_iff.mpr ?_
            intro ε hε
            use ε, hε
            intro y hy_s hy_dist
            have hx_s : x ∈ s := interior_subset hx_interior
            calc dist (g.toFun y) (g.toFun x)
                = dist y x := g.isometry_on_pieces s hs_g y hy_s x hx_s
              _ < ε := hy_dist
          -- Apply continuity: x ∈ closure (g⁻¹ t ∩ s) implies g(x) ∈ closure (g(g⁻¹ t ∩ s))
          have hx_closure_inter : x ∈ closure (g.toFun ⁻¹' t ∩ s) := by
            -- x ∈ closure (g⁻¹ t) and x ∈ closure s, and s is in the partition (hence closed? No, not necessarily)
            -- Better: x ∈ interior s ⊆ s, and x ∈ closure (g⁻¹ t)
            -- We want to show x ∈ closure (g⁻¹ t ∩ s)
            -- Use: closure A ∩ B ⊆ closure (A ∩ B) when B is closed
            -- But s might not be closed. Instead, use directly:
            have hx_s : x ∈ s := interior_subset hx_interior
            -- x ∈ s ∩ closure (g⁻¹ t) ⊆ closure (g⁻¹ t ∩ s) if s is open
            -- Actually, x ∈ interior s means there's a neighborhood U ⊆ s with x ∈ U
            -- and x ∈ closure (g⁻¹ t) means every neighborhood of x intersects g⁻¹ t
            -- So U ∩ g⁻¹ t is nonempty, and U ∩ g⁻¹ t ⊆ s ∩ g⁻¹ t
            -- Hence x ∈ closure (s ∩ g⁻¹ t) = closure (g⁻¹ t ∩ s)
            rw [mem_closure_iff_nhds]
            intro U hU
            rw [mem_closure_iff_nhds] at hx_closure
            -- Need to show U ∩ (g⁻¹ t ∩ s) is nonempty
            -- We have x ∈ interior s, so there exists V open with x ∈ V ⊆ s
            -- Then U ∩ V is a neighborhood of x
            -- Since x ∈ closure (g⁻¹ t), we have (U ∩ V) ∩ g⁻¹ t nonempty
            -- And (U ∩ V) ∩ g⁻¹ t ⊆ U ∩ (g⁻¹ t ∩ s)
            obtain ⟨V, hV_subset, hV_open, hxV⟩ := mem_interior.mp hx_interior
            have hUV : U ∩ V ∈ nhds x := Filter.inter_mem hU (hV_open.mem_nhds hxV)
            have hUVt : (U ∩ V ∩ g.toFun ⁻¹' t).Nonempty :=
              hx_closure (U ∩ V) hUV
            -- Now show U ∩ (g⁻¹ t ∩ s) is nonempty using hUVt
            obtain ⟨y, hy⟩ := hUVt
            simp [Set.mem_inter_iff] at hy
            use y
            simp [Set.mem_inter_iff]
            exact ⟨hy.1.1, hy.2, hV_subset hy.1.2⟩
          -- Need g continuous within (g⁻¹ t ∩ s) at x
          have g_cont_within_inter : ContinuousWithinAt g.toFun (g.toFun ⁻¹' t ∩ s) x := by
            apply ContinuousWithinAt.mono g_cont_within
            exact Set.inter_subset_right
          have : g.toFun x ∈ closure (g.toFun '' (g.toFun ⁻¹' t ∩ s)) :=
            ContinuousWithinAt.mem_closure_image g_cont_within_inter hx_closure_inter
          refine closure_mono ?_ this
          -- g '' (g⁻¹ t ∩ s) ⊆ t
          intro y hy
          obtain ⟨z, ⟨hz_preimage, hz_s⟩, rfl⟩ := hy
          exact hz_preimage
        · -- g(x) ∉ interior t
          have hx_not_int : x ∉ interior (g.toFun ⁻¹' t) := hx_right.2.2
          intro hgx_int
          -- If g(x) ∈ interior t, use continuity to get x ∈ interior (g⁻¹ t)
          have g_cont_within : ContinuousWithinAt g.toFun s x := by
            refine Metric.continuousWithinAt_iff.mpr ?_
            intro ε hε
            use ε, hε
            intro y hy_s hy_dist
            have hx_s : x ∈ s := interior_subset hx_interior
            calc dist (g.toFun y) (g.toFun x)
                = dist y x := g.isometry_on_pieces s hs_g y hy_s x hx_s
              _ < ε := hy_dist
          -- interior t is open and contains g(x)
          have : g.toFun ⁻¹' interior t ∈ nhdsWithin x s := by
            apply g_cont_within
            exact isOpen_interior.mem_nhds hgx_int
          -- Since x ∈ interior s, nhdsWithin x s = nhds x locally
          have hx_nhds : nhdsWithin x s = nhds x := by
            exact nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hx_interior)
          rw [hx_nhds] at this
          -- So g⁻¹(interior t) is a neighborhood of x
          -- This means x ∈ interior (g⁻¹(interior t)) ⊆ interior (g⁻¹ t)
          have : x ∈ interior (g.toFun ⁻¹' interior t) := mem_interior_iff_mem_nhds.mpr this
          have : x ∈ interior (g.toFun ⁻¹' t) := by
            refine interior_mono ?_ this
            exact Set.preimage_mono interior_subset
          exact hx_not_int this
      left
      right
      rw [Set.mem_preimage, Set.mem_iUnion]
      use t
      rw [Set.mem_iUnion]
      exact ⟨ht_f, hgx_frontier⟩
    · -- x is not in interior of s, so x ∈ frontier s (since x ∈ closure s)
      have hx_frontier_s : x ∈ frontier s := by
        rw [frontier, Set.mem_diff]
        exact ⟨hx_right.1, hx_interior⟩
      right
      exact ⟨s, hs_g, hx_frontier_s⟩

end CompositionProperties

section IterationProperties

/-- The discontinuity set of an iterate grows with iteration. -/
theorem discontinuitySet_iterate [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (n : ℕ) :
    (iterate f n).discontinuitySet ⊆ ⋃ k < n, f.toFun^[k] ⁻¹' f.discontinuitySet := by
  induction n with
  | zero =>
    -- iterate 0 = id, discontinuity set is empty or just frontiers of {univ}
    intro x hx
    -- id has partition {univ}, so discontinuity set is frontier univ = ∅
    rw [iterate_zero_eq] at hx
    unfold id discontinuitySet at hx
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, hs, hx_frontier⟩ := hx
    rw [hs] at hx_frontier
    rw [frontier_univ] at hx_frontier
    exact absurd hx_frontier (Set.notMem_empty x)
  | succ n ih =>
    -- iterate (n+1) = f.comp (iterate n)
    rw [iterate_succ]
    intro x hx
    -- Apply discontinuitySet_comp_subset
    have h_comp := discontinuitySet_comp_subset f (iterate f n)
    have hx_in : x ∈ f.discontinuitySet ∪ ((iterate f n).toFun ⁻¹' f.discontinuitySet) ∪
                     (iterate f n).discontinuitySet := h_comp hx
    simp only [Set.mem_union] at hx_in
    simp only [Set.mem_iUnion]
    rcases hx_in with (hx_f | hx_preimage) | hx_iterate_n
    · -- x ∈ f.discontinuitySet = f^[0]⁻¹(f.discontinuitySet)
      use 0, Nat.zero_lt_succ n
      simp [Function.iterate_zero, Set.preimage_id]
      exact hx_f
    · -- x ∈ (iterate f n)⁻¹(f.discontinuitySet) = f^[n]⁻¹(f.discontinuitySet)
      use n, Nat.lt_succ_self n
      rw [iterate_toFun] at hx_preimage
      exact hx_preimage
    · -- x ∈ (iterate f n).discontinuitySet
      -- By IH, x ∈ ⋃ k < n, f^[k]⁻¹(f.discontinuitySet)
      have hx_union := ih hx_iterate_n
      simp only [Set.mem_iUnion] at hx_union
      obtain ⟨k, hk_lt, hx_k⟩ := hx_union
      use k, Nat.lt_trans hk_lt (Nat.lt_succ_self n)

/-- If f has finitely many discontinuities, so does each iterate (though possibly more). -/
theorem iterate_finite_discontinuities [Nonempty α] [BorelSpace α] (f : PiecewiseIsometry α) (n : ℕ)
    (hf : f.discontinuitySet.Finite) :
    (iterate f n).discontinuitySet.Finite := by
  -- Use discontinuitySet_iterate: (iterate f n).discontinuitySet ⊆ ⋃ k < n, f^[k]⁻¹(f.discontinuitySet)
  -- This is a finite union of preimages of a finite set
  -- However, preimages of finite sets need not be finite without injectivity

  -- PROOF ATTEMPT: This theorem appears to require additional assumptions
  -- Without injectivity/bijectivity of f, preimages of finite sets can be infinite
  -- For example, a constant map has infinite preimage of any point

  -- However, if we assume f is injective on each piece, we might be able to proceed
  -- But that's not part of the current structure definition

  -- Alternative: The discontinuity set is contained in partition boundaries,
  -- which are themselves related to the original partition
  -- Let me try to use a different approach based on partition properties

  /- PROOF ATTEMPTS:

  Attempt 1 [2025-10-16]:
  Strategy: Use discontinuitySet_iterate to bound by finite union, then argue preimages are finite
  Failure: Preimages of finite sets need not be finite without injectivity
  Lesson: Need stronger hypothesis (e.g., f injective) or different approach

  Attempt 2 [2025-10-16]:
  Strategy: Use that discontinuity set is union of partition piece boundaries
  Failure: Refined partitions can have more pieces, boundaries can grow
  Lesson: The partition refinement doesn't preserve finiteness of boundary points directly

  CURRENT STATUS: This theorem likely requires additional hypotheses:
  - Either f is injective (or bijective)
  - Or f has some bounded-fiber property
  - Or we work with a different notion of "finite discontinuities"

  This is mathematically non-trivial and may require rethinking the statement.
  -/
  sorry

end IterationProperties

end PiecewiseIsometry
