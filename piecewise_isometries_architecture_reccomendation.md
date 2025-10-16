# Formalizing Piecewise Isometries in mathlib4

**The foundation exists, but the specific structure needs careful design.** Mathlib4 provides robust infrastructure for isometries, piecewise functions, metric spaces, and dynamical systems. The recommended approach is a three-tiered structure pattern (basic property → full structure → relaxed variant) following successful ergodic theory contributions, with measure-preserving and continuity properties handled separately. Start with incremental PRs focusing on core definitions, engage the community on Zulip early, and follow strict naming and documentation conventions.

This report synthesizes the current mathlib4 landscape for piecewise isometries, provides concrete design recommendations based on successful similar contributions, and outlines the contribution process with actionable guidance.

## Available mathlib4 structures to leverage

Mathlib4 provides extensive foundational infrastructure that directly supports piecewise isometry formalization. The key is understanding what exists and how to compose these elements effectively.

### Isometries: The core building block

**Two complementary approaches** exist for isometries in `Mathlib.Topology.MetricSpace.Isometry`:

The **`Isometry` predicate** defines isometric functions as distance-preserving maps. For a function `f : α → β` between metric spaces, `Isometry f` means `∀ x y, dist (f x) (f y) = dist x y`. This unbundled predicate comes with rich API including **`Isometry.continuous`** (every isometry is continuous), **`Isometry.comp`** (composition preserves the property), and **`Isometry.dimH_image`** (Hausdorff dimension preservation).

The **`IsometryEquiv` structure** (notation `α ≃ᵢ β`) bundles equivalences with isometry proofs. It extends the equivalence `α ≃ β` and adds `isometry_toFun : Isometry toFun`. This structure provides `symm` for inverses, `trans` for composition, and automatic continuity. For piecewise isometries where each piece maps isometrically, this is your primary tool.

```lean
-- Example usage
example (α β : Type*) [MetricSpace α] [MetricSpace β] 
  (f : α → β) (hf : Isometry f) (x y : α) :
  dist (f x) (f y) = dist x y :=
hf.dist_eq x y
```

**Key imports needed:**
```lean
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Module.LinearIsometry  -- for linear isometries
```

### Piecewise functions: The compositional mechanism

**`Set.piecewise`** from `Mathlib.Analysis.Convex.Piecewise` is mathlib4's standard approach for piecewise-defined functions. Given a set `s`, two functions `f` and `g`, it constructs `s.piecewise f g` which equals `f` on `s` and `g` on `sᶜ`.

```lean
def Set.piecewise (s : Set α) (f g : α → β) [∀ x, Decidable (x ∈ s)] : α → β :=
  fun x => if x ∈ s then f x else g x
```

Properties like **`Set.piecewise_eq_of_mem`** and **`Set.piecewise_eq_of_not_mem`** establish behavior on each piece. For piecewise isometries with multiple pieces, you'll need to iterate this construction or use a more general partition representation.

**Set operations** from `Mathlib.Data.Set.Function` provide crucial tools: `Set.EqOn f₁ f₂ s` (functions agree on set), `Set.InjOn` (injective on set), `Set.BijOn` (bijective between sets). These enable proving isometry properties piece-by-piece.

### Measure theory and dynamical systems: The context

For piecewise isometries as dynamical systems, mathlib4's `Mathlib.Dynamics.Ergodic` directory provides excellent precedents.

**`MeasurePreserving`** from `Mathlib.Dynamics.Ergodic.MeasurePreserving` combines measurability with measure equation:

```lean
structure MeasurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) (ν : Measure β) where
  measurable : Measurable f
  map_eq : Measure.map f μ = ν
```

This structure provides `comp` for composition, `symm` for inverses of equivalences, and connections to ergodic theory. The **three-tiered structure pattern** in ergodic theory (PreErgodic → Ergodic → QuasiErgodic) demonstrates how to separate core properties from technical requirements using `extends`.

**Ergodic structures** show how to handle dynamical properties:

```lean
structure Ergodic (f : α → α) (μ : Measure α) extends
  MeasureTheory.MeasurePreserving f μ μ,
  PreErgodic f μ
```

For piecewise isometries, you could similarly define `PiecewiseIsometry` as base, then extend to `MeasurePreservingPiecewiseIsometry` and `ErgodicPiecewiseIsometry`.

### Current gaps requiring new development

**Interval exchange transformations do not exist** in mathlib4 yet. This represents both a gap and an opportunity - you can establish precedents for piecewise-defined dynamical systems. **No dedicated partition structure** exists; instead, partitions are represented as collections of disjoint measurable sets with covering properties. **No explicit discontinuity set formalization** exists; discontinuities are handled through complements of continuity sets or measure-theoretic null sets.

## Best practices for mathlib4 contributions

Understanding mathlib4's contribution standards is critical for successful submissions. The community has established strict conventions that enable maintainability and consistency across 1.5 million lines of formalized mathematics.

### The contribution workflow

**Engage on Zulip first.** Before writing code, join https://leanprover.zulipchat.com/ and post in #mathlib4 introducing your project. Describe what you want to formalize and ask for feedback. Maintainers particularly active in dynamics and measure theory include Rémy Degenne, Floris van Doorn, Sébastien Gouëzel, and Yury Kudryashov.

**Fork and setup** from https://github.com/leanprover-community/mathlib4. After cloning, run `lake exe cache get` to download cached build files (crucial for compilation speed). Create a feature branch: `git switch -c piecewise-isometry`. If you add new files, run `lake exe mk_all` to update the master index.

**Keep PRs small and focused.** A PR adding just the basic structure definition with 2-3 simple lemmas and examples (under 200 lines) will be reviewed much faster than a 1000-line PR with complete API. Break large contributions into 5-10 small PRs that build incrementally. Each PR must compile without `sorry` placeholders and pass CI tests.

### File organization and structure

**Headers are mandatory.** Every file starts with:

```lean
/-
Copyright (c) 2024 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Dynamics.Ergodic.MeasurePreserving
```

**Module docstrings follow immediately** after imports using `/-! -/`:

```lean
/-!
# Piecewise isometries

In this file we define piecewise isometries on metric spaces,
which are maps that restrict to isometries on each piece of a partition.

## Main definitions
- `PiecewiseIsometry`: A map defined by local isometries on partition pieces
- `PiecewiseIsometry.discontinuitySet`: The set of discontinuity points

## Main results
- `PiecewiseIsometry.measurePreserving`: Under appropriate conditions, 
  piecewise isometries preserve measure

## Notation
- `f^[n]` : The nth iterate of piecewise isometry `f`

## References
See [Adler2001] for background on piecewise isometries.
-/
```

**Directory structure** should follow existing patterns. Propose placing piecewise isometries in `Mathlib/Dynamics/PiecewiseIsometry/` with subdirectory structure:
- `Basic.lean` - core definitions
- `Properties.lean` - basic properties and lemmas  
- `Examples.lean` - standard examples
- `Ergodic.lean` - connections to ergodic theory

### Code style requirements

**Line length: 100 characters maximum.** VS Code shows a visual marker. **Indentation: 2 spaces for proof content**, 4 spaces for continuation of multi-line declarations. Top-level declarations are flush-left. Namespace and section contents are not indented.

**Tactic mode conventions:**
```lean
theorem piecewise_isometry_preserves_dist {α : Type*} [MetricSpace α]
    (f : PiecewiseIsometry α) (x y : α) (h : x ∈ s) (hs : s ∈ f.partition) :
    dist (f x) (f y) = dist x y := by
  apply f.isometry_on s hs
  · exact h
  · exact sorry  -- NEVER commit sorry; this is just example
```

Use focusing dots `·` (typed `\.`) for subgoals. Put `by` at end of declaration line, not on its own line. Prefer `fun x ↦ x * x` (with `↦` typed `\mapsto`) over lambda notation.

**Whitespace rules:** Use `<|` instead of `$` (dollar sign is disallowed in mathlib). Add spaces around `:`, `:=`, and infix operators. For `rw` and `simp`, add space after left arrow: `rw [← add_comm a b]`.

### Naming conventions decoded

Mathlib4 uses context-specific capitalization: **Prop-valued terms use snake_case**, **structures and types use UpperCamelCase**, **functions follow their return value conventions**.

For piecewise isometries:
- Structure: `PiecewiseIsometry` (UpperCamelCase)
- Fields: `partition`, `isometry_on`, `discontinuity_set` (snake_case)
- Theorems: `piecewise_isometry_comp`, `measurePreserving_of_null_discontinuities`

**Theorem naming patterns** describe conclusions with hypotheses separated by "of":
- `isometry_of_piecewise` - isometry property follows from piecewise construction
- `continuous_of_finite_discontinuities` - continuity from finiteness hypothesis
- `ergodic_iff_irreducible` - bidirectional characterization

**Symbol-to-name dictionary:**
- `∀` → `forall` / `all`
- `∃` → `exists`
- `∧` → `and`
- `∨` → `or`
- `→` → `of` / `imp`
- `↔` → `iff`
- `≤` → `le`
- `<` → `lt`

### Documentation standards

**Every definition needs a docstring.** Theorems benefit from docstrings, especially for mathematical content:

```lean
/-- A piecewise isometry is a map on a metric space that restricts to 
an isometry on each piece of a measurable partition. The discontinuities 
occur only at partition boundaries. -/
structure PiecewiseIsometry (α : Type*) [MetricSpace α] [MeasurableSpace α] where
  /-- The measurable partition of the domain -/
  partition : Set (Set α)
  /-- Each piece is measurable -/
  partition_measurable : ∀ s ∈ partition, MeasurableSet s
  ...
```

Docstrings support **LaTeX math** with `$ ... $` for inline and `$$ ... $$` for display. Use backticks for code references: `` `PiecewiseIsometry` ``. Fully-qualified names become links: `` `Mathlib.Dynamics.PiecewiseIsometry.Basic` ``.

### PR review process and lifecycle

**CI must pass** before reviewers will look at your PR. Green checkmark on GitHub indicates success. PRs appear on the review queue at https://leanprover-community.github.io/queueboard/review_dashboard.html within hours if properly formatted.

**Review cycle:**
1. Reviewer adds comments and "awaiting-author" label
2. Address feedback, resolve conversations, remove "awaiting-author"
3. Repeat until reviewer satisfied
4. Reviewer adds "maintainer-merge" label
5. Maintainer gives final approval → "ready-to-merge" label
6. Bors bot automatically merges from queue

**PR title format** follows commit conventions: `feat(Dynamics): add PiecewiseIsometry structure`. Types include `feat` (new feature), `fix` (bug fix), `doc` (documentation), `refactor` (restructuring). Use imperative mood: "add" not "adds" or "added".

## The right approach for defining piecewise isometries

Based on analysis of successful similar contributions, particularly the ergodic theory structures, here's the recommended design approach with concrete code patterns.

### Design choice: Structure vs class vs predicate

**Use structure** for piecewise isometries. This follows mathlib4's pattern for morphisms and complex mathematical objects. Compare the isometry precedent: `Isometry` is an unbundled predicate (`Isometry f : Prop`), while `IsometryEquiv` is a bundled structure. For piecewise isometries, you're defining objects with multiple components (partition, local maps, proofs), making structure the right choice.

**Reserve typeclasses (class)** for properties that should be inferred automatically, like algebraic structures or topological properties. Piecewise isometry is a specific kind of map, not a property to be inferred.

**Use predicates** for lighter-weight properties. You might define `IsPiecewiseIsometry (f : α → α) : Prop` as a companion to the bundled structure, useful for stating theorems about existing functions.

### Recommended three-tiered structure pattern

Follow the successful ergodic theory pattern with separation of concerns:

**Tier 1: Core structure without additional constraints**

```lean
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-- A piecewise isometry on a metric space with a measurable partition. -/
structure PiecewiseIsometry (α : Type*) [MetricSpace α] [MeasurableSpace α] where
  /-- The partition pieces -/
  partition : Set (Set α)
  /-- Each piece is measurable -/
  partition_measurable : ∀ s ∈ partition, MeasurableSet s
  /-- The pieces partition α -/
  partition_cover : ⋃₀ partition = Set.univ
  /-- The pieces are pairwise disjoint -/
  partition_disjoint : partition.PairwiseDisjoint id
  /-- The underlying function -/
  toFun : α → α
  /-- Isometry property on each piece -/
  isometry_on_pieces : ∀ s ∈ partition, ∀ x y ∈ s,
    dist (toFun x) (toFun y) = dist x y

namespace PiecewiseIsometry

instance : CoeFun (PiecewiseIsometry α) (fun _ => α → α) where
  coe f := f.toFun

/-- The set of discontinuities is contained in partition boundaries -/
def discontinuitySet (f : PiecewiseIsometry α) : Set α :=
  ⋃ s ∈ f.partition, frontier s

end PiecewiseIsometry
```

**Tier 2: Measure-preserving version**

```lean
/-- A measure-preserving piecewise isometry. -/
structure MeasurePreservingPiecewiseIsometry (α : Type*) 
    [MetricSpace α] [MeasurableSpace α] (μ : Measure α)
    extends PiecewiseIsometry α where
  measurable_toFun : Measurable toFun
  measure_preserving : MeasureTheory.MeasurePreserving toFun μ μ
```

**Tier 3: Ergodic version**

```lean
/-- An ergodic piecewise isometry. -/
structure ErgodicPiecewiseIsometry (α : Type*)
    [MetricSpace α] [MeasurableSpace α] (μ : Measure α)
    extends MeasurePreservingPiecewiseIsometry α μ where
  ergodic : Ergodic toFun μ
```

This pattern allows users to work at the appropriate generality level and provides clear extension paths.

### Handling partitions and discontinuities

**Represent partitions** as `Set (Set α)` with explicit disjointness and covering conditions. Don't create a separate `Partition` type initially - this can be abstracted later if needed. Use `partition.PairwiseDisjoint id` for disjointness and `⋃₀ partition = Set.univ` for covering.

**For finite partitions**, add a separate structure or constraint:

```lean
structure FinitePiecewiseIsometry (α : Type*) [MetricSpace α] [MeasurableSpace α]
    extends PiecewiseIsometry α where
  partition_finite : partition.Finite
```

**Discontinuity sets** should be defined through boundary/frontier operations:

```lean
def discontinuitySet (f : PiecewiseIsometry α) : Set α :=
  ⋃ s ∈ f.partition, frontier s
  
theorem discontinuitySet_measurable (f : PiecewiseIsometry α) :
    MeasurableSet (discontinuitySet f) := by
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro hs
  exact MeasurableSet.frontier (f.partition_measurable s hs)
```

**Prove measure-zero discontinuities** when appropriate:

```lean
theorem measurePreserving_of_null_discontinuities 
    [MeasurableSpace α] (μ : Measure α) (f : PiecewiseIsometry α)
    (h_meas : Measurable f.toFun)
    (h_null : μ (discontinuitySet f) = 0) :
    MeasureTheory.MeasurePreserving f.toFun μ μ := by
  sorry  -- Proof strategy: measure preservation on each piece + null boundaries
```

### Composition and iteration patterns

**Composition requires partition refinement.** When composing piecewise isometries, the resulting partition is the common refinement:

```lean
def comp (f g : PiecewiseIsometry α) : PiecewiseIsometry α where
  partition := {s ∩ t | s ∈ g.partition ∧ t ∈ f.partition ∧ (s ∩ t).Nonempty}
  partition_measurable := by
    intro s hs
    obtain ⟨s₁, hs₁, t₁, ht₁, _, rfl⟩ := hs
    exact (g.partition_measurable s₁ hs₁).inter (f.partition_measurable t₁ ht₁)
  toFun := f.toFun ∘ g.toFun
  isometry_on_pieces := by
    intro s hs x hx y hy
    sorry  -- Apply isometry property to each component
```

**Iteration** uses Lean's standard `Function.iterate` notation:

```lean
def iterate (f : PiecewiseIsometry α) : ℕ → (α → α)
  | 0 => id
  | n + 1 => f.toFun ∘ iterate f n

notation f "^[" n "]" => iterate f n

theorem iterate_isometry (f : PiecewiseIsometry α) (n : ℕ) :
    IsPiecewiseIsometry (f^[n]) := by
  sorry  -- Induction on n
```

### Alternative lightweight approach

For initial development or simpler use cases, consider an **unbundled predicate**:

```lean
/-- A function is a piecewise isometry if there exists a partition
on which it restricts to isometries. -/
def IsPiecewiseIsometry {α : Type*} [MetricSpace α] (f : α → α) : Prop :=
  ∃ (partition : Set (Set α)),
    (∀ s ∈ partition, MeasurableSet s) ∧
    (⋃₀ partition = Set.univ) ∧
    (partition.PairwiseDisjoint id) ∧
    (∀ s ∈ partition, ∀ x y ∈ s, dist (f x) (f y) = dist x y)

theorem Isometry.isPiecewiseIsometry {α : Type*} [MetricSpace α] 
    (f : α → α) (hf : Isometry f) :
    IsPiecewiseIsometry f := by
  use {Set.univ}
  constructor
  · intro s hs
    simp at hs
    rw [hs]
    exact MeasurableSet.univ
  sorry  -- Complete remaining conditions
```

This lightweight approach enables stating properties about existing functions without requiring bundled structures, useful for connecting to existing mathlib4 theory.

### Concrete example: Interval exchange transformations

As a specific application, interval exchange transformations fit naturally into this framework:

```lean
structure IntervalExchangeTransformation where
  n : ℕ
  n_pos : 0 < n
  lengths : Fin n → ℝ
  lengths_pos : ∀ i, 0 < lengths i
  permutation : Equiv.Perm (Fin n)

def IntervalExchangeTransformation.toPiecewiseIsometry 
    (iet : IntervalExchangeTransformation) : 
    PiecewiseIsometry (Set.Icc (0 : ℝ) 1) where
  partition := sorry  -- Construct subintervals from lengths
  partition_measurable := sorry
  partition_cover := sorry
  partition_disjoint := sorry
  toFun := sorry  -- Apply permutation and translate
  isometry_on_pieces := sorry  -- Translations are isometries
```

This demonstrates how piecewise isometries serve as a general framework for specific dynamical systems.

### Incremental development strategy

**PR 1: Core definitions** (150-200 lines)
- `PiecewiseIsometry` structure
- `CoeFun` instance  
- `discontinuitySet` definition
- 2-3 basic examples (identity, rotation)

**PR 2: Basic API** (150-200 lines)
- Constructor helpers
- Basic properties (partition coverage, disjointness lemmas)
- Connection to `Isometry` predicate

**PR 3: Composition** (150-200 lines)
- `comp` definition
- Composition properties
- Identity and associativity

**PR 4: Measure theory** (200-250 lines)
- `MeasurePreservingPiecewiseIsometry` structure
- Measure preservation proofs
- Null discontinuity set theorems

**PR 5: Ergodic properties** (200-250 lines)
- Connection to `Ergodic` structure
- Ergodicity criteria
- Examples from billiards or IETs

This incremental approach enables faster review cycles and allows feedback to shape subsequent contributions.

## Conclusion

Formalizing piecewise isometries in mathlib4 is highly feasible with existing infrastructure. The isometry API, piecewise function support, and measure-preserving dynamical systems framework provide solid foundations. The three-tiered structure pattern from ergodic theory offers an excellent template for separating core properties from technical requirements. Success requires strict adherence to mathlib4 conventions, early community engagement on Zulip, and incremental PRs that build API methodically. With no interval exchange transformations formalized yet, this contribution could establish important precedents for piecewise-defined dynamical systems in mathlib4.