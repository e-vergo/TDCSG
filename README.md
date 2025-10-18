# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Goal:** Formalize Theorem 2 - proving that GG₅ has critical radius r_c = √(3 + φ) via emergence of a 3-interval exchange transformation.

## Current Status

**Build:** ✅ 16/16 files compile without errors
**Sorries:** 62 strategic sorries across 9 files (7 files proof-complete)
**Phase:** Scaffolding complete, ready for systematic proof development

### Proof-Complete Files (0 sorries)
- `TDCSG.Basic` - Piecewise isometry framework
- `TDCSG.Composition` - Composition and iteration
- `TDCSG.Finite` - Finite partition specializations
- `TDCSG.IntervalExchange` - IET infrastructure (critical for Theorem 2)
- `TDCSG.MeasurePreserving` - Measure-preserving transformations
- `TDCSG.Properties` - Partition and isometry lemmas
- `TDCSG.Examples` - Proven examples and counterexamples

### Files with Strategic Sorries

**GG5 Theorem Infrastructure (39 sorries):**
- `Geometry.lean` - 18 sorries (geometric construction lemmas)
- `IET.lean` - 14 sorries (interval exchange emergence proof)
- `SegmentMaps.lean` - 7 sorries (bijections and isometries)

**Two-Disk System (11 sorries):**
- `TwoDisk.lean` - 11 sorries (partition properties, generator isometries)

**Planar Geometry (5 sorries):**
- `Disks.lean` - 3 sorries (overlap criteria, measurability)
- `Rotations.lean` - 2 sorries (periodicity lemmas)

**Other (7 sorries):**
- `CriticalRadius.lean` - 2 sorries (basic properties of r_crit)
- `Finiteness.lean` - 1 sorry (Theorem 1 statement)

## What Are Two-Disk Compound Symmetry Groups?

The two-disk system GG_{n₁,n₂}(r₁, r₂) consists of:
- Two overlapping closed disks in ℝ² centered at (-1, 0) and (1, 0) with radii r₁, r₂
- Generator **a**: rotation by 2π/n₁ on the left disk
- Generator **b**: rotation by 2π/n₂ on the right disk
- Group elements are finite compositions of a and b, acting as piecewise isometries on ℝ²

**Critical phenomenon:** As radius increases, these groups undergo a phase transition from finite to infinite at a critical radius. At this transition point, remarkable structures emerge.

**Theorem 2:** For GG₅ (the n=5 case):
- Critical radius r_c = √(3 + φ) where φ is the golden ratio
- At r_c, three group elements piecewise map a line segment E'E onto itself
- This forms a **3-interval exchange transformation** embedded in the 2D system
- The IET has irrational length ratios involving φ → infinite orbit → group is infinite

## Project Structure

```
TDCSG/
├── check_lean.sh              # Main build verification tool
├── tools/                     # Tool implementation
│   ├── CHECK_LEAN_TOOL.md    # Complete tool documentation
│   ├── check_lean_errors_only.py
│   ├── check_lean_sorries.py
│   ├── check_lean_transparency.py  # Proof quality enforcement
│   └── test_error_detection.sh    # Regression tests
│
├── TDCSG/                     # Lean formalization
│   ├── Basic.lean            # ✅ Piecewise isometry framework
│   ├── Properties.lean       # ✅ Isometry and partition lemmas
│   ├── Composition.lean      # ✅ Composition theory
│   ├── MeasurePreserving.lean # ✅ Measure theory integration
│   ├── Finite.lean           # ✅ Finite partition specializations
│   ├── IntervalExchange.lean # ✅ IET infrastructure (needed for Theorem 2)
│   ├── Examples.lean         # ✅ Proven examples and counterexamples
│   ├── Ergodic.lean          # (Research-level, not imported in main)
│   │
│   ├── Planar/               # 2D geometric primitives
│   │   ├── Rotations.lean   # rotateAround using Mathlib infrastructure
│   │   └── Disks.lean       # Disk geometry and overlap properties
│   │
│   └── CompoundSymmetry/     # Two-disk systems and Theorem 2
│       ├── TwoDisk.lean      # Core two-disk system structure
│       ├── Finiteness.lean   # Critical radius definition
│       └── GG5/              # Theorem 2 proof infrastructure
│           ├── Geometry.lean     # Points E, E', F, G; r_crit definition
│           ├── SegmentMaps.lean  # Three group elements on segment
│           ├── IET.lean          # IET emergence theorem
│           └── CriticalRadius.lean # Basic properties of r_crit
│
├── CLAUDE.md                  # Rigor standards and anti-placeholder protocol
└── README.md                  # This file
```

## Quick Start

### Prerequisites

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone <repository-url>
cd TDCSG
lake build
```

### Development Workflow

**1. Fast iteration** (use constantly):
```bash
./check_lean.sh --errors-only TDCSG/File.lean
```

**2. Track proof progress:**
```bash
./check_lean.sh --sorries TDCSG/File.lean
```

**3. Project-wide status:**
```bash
./check_lean.sh --all errors-only TDCSG/
./check_lean.sh --all sorries TDCSG/
```

**4. Before committing:**
```bash
./check_lean.sh --transparency TDCSG/File.lean
```

## Build Tool: check_lean.sh

**Why:** Raw `lake build` output is 50,000-100,000 tokens per file. Our tool reduces this to 500-1,000 tokens (**99% reduction**) while providing complete diagnostics.

| Mode | Purpose | Use Case |
|------|---------|----------|
| `--errors-only` | Fast compilation check | Every iteration |
| `--sorries` | Track incomplete proofs | Monitor progress |
| `--warnings-summary` | Categorized warnings | Code quality |
| `--transparency` | Proof quality enforcement | Pre-commit validation |
| `--all <mode>` | Multi-file aggregation | Project status |

**Key features:**
- Per-file error filtering (no noise from dependencies)
- Never clips error messages
- Detects proof evasion patterns (trivial abuse, placeholders)
- Exit codes for automation
- 99% token reduction vs raw lake build

**Full documentation:** [tools/CHECK_LEAN_TOOL.md](tools/CHECK_LEAN_TOOL.md)

## Rigor Standards

Zero-tolerance proof quality enforced via `./check_lean.sh --transparency`.

### Forbidden Patterns

❌ `theorem foo : True := trivial` - No mathematical content
❌ `def IsPredicate := True` - Trivializes dependent theorems
❌ Custom axioms, `admitted`, `unsafe` keywords
❌ Hidden sorries or `sorryAx` dependencies

### Completion Criteria

A `sorry` is only complete when:
- ✅ Theorem proves the actual proposition (not `True`)
- ✅ Proof uses legitimate tactics deriving the goal
- ✅ Zero custom axioms
- ✅ `./check_lean.sh --errors-only` passes
- ✅ `./check_lean.sh --transparency` passes
- ✅ Mathlib-quality code

**Philosophy:** Every theorem must meet publication-grade standards. No shortcuts.

**See [CLAUDE.md](CLAUDE.md) for complete protocol.**

## Next Steps: Proof Development Plan

### Priority 1: TwoDisk.lean (11 sorries)

**Goal:** Complete the core two-disk system infrastructure.

**Sorries to prove:**
1. `basicPartition_countable` - The partition is countable (easy)
2. `basicPartition_measurable` - Partition pieces are measurable (straightforward)
3. `basicPartition_cover` - Partition covers the space (moderate)
4. `basicPartition_disjoint` - Pieces are pairwise disjoint (moderate)
5. `basicPartition_nonempty` - Each piece is nonempty (easy)
6. `genA_isometry_on_leftDisk` - Generator a preserves distances on left disk (use rotateAround properties)
7. `genB_isometry_on_rightDisk` - Generator b preserves distances on right disk (similar)
8. `genA_eq_id_on_compl` - Generator a is identity outside left disk (by definition)
9. `genB_eq_id_on_compl` - Generator b is identity outside right disk (by definition)

**Why first:** This unlocks the ability to work with concrete two-disk systems.

**Strategy:**
- Use Mathlib's `Metric.closedBall` properties
- Leverage `rotateAround` isometry proofs from Rotations.lean
- Classical decidability for if-expressions

### Priority 2: Planar Geometry (5 sorries)

**Rotations.lean (2 sorries):**
1. `rotateAround_iterate_aux` - Rotation iteration identity
2. `rotateAround_periodic` - Rotation by 2π/n has period n

**Disks.lean (3 sorries):**
1. `disks_overlap_iff` - Distance criterion for overlap
2. `disk_inter_measurable` - Intersection is measurable
3. `disk_inter_compact` - Intersection is compact

**Why:** Needed for partition proofs in TwoDisk.lean

**Strategy:**
- Use Mathlib's metric space lemmas
- Compactness from closed + bounded

### Priority 3: GG5 Geometry (18 sorries)

**Focus areas:**
1. **Basic properties** (4 sorries): r_crit_pos, zeta5 properties
2. **Point definitions** (5 sorries): E, F, G positions and relationships
3. **Transformations** (3 sorries): How group elements act on segment
4. **Golden ratio connections** (6 sorries): Segment ratios and irrationality

**Why:** These are the geometric facts needed for the IET emergence proof

**Strategy:**
- Heavy use of Complex number arithmetic from Mathlib
- `Real.goldenRatio` and `Real.goldenRatio_sq` properties
- Coordinate geometry in ℝ²

### Priority 4: Segment Maps & IET (21 sorries)

**SegmentMaps.lean (7 sorries):**
- Prove the three bijections: E'F→GF, FG→FE, GE→E'G
- Show they are isometries
- Prove irrational translation lengths

**IET.lean (14 sorries):**
- Show interval lengths are positive
- Prove they sum to 1
- Establish golden ratio relationships
- Connect segment dynamics to IET structure

**Why:** This is the core of Theorem 2 - the IET emergence

**Strategy:**
- Use completed Geometry.lean lemmas
- Leverage `IntervalExchange.lean` infrastructure
- Careful geometric calculations

### Priority 5: Final Assembly (2 sorries)

**CriticalRadius.lean (2 sorries):**
1. `critical_radius_pos` - r_crit > 0
2. `critical_radius_polynomial` - Polynomial relation for r_crit

**Why last:** These are simple algebraic facts, save for end

## Mathlib Dependencies

**We use:**
- `Metric.closedBall` - Closed balls (disks)
- `Orientation.rotation` - Linear rotations in ℝ²
- `AffineIsometryEquiv` - Affine isometric equivalences
- `Real.goldenRatio` - The golden ratio φ
- `Real.goldenRatio_irrational` - φ is irrational
- `MulAction.orbit` - Group orbits
- Complex number arithmetic

**We build:**
- `rotateAround` - Rotation about arbitrary point
- `TwoDiskSystem` - Compound symmetry group structure
- Piecewise isometry framework
- IET infrastructure (not in Mathlib)
- Connection between 2D piecewise isometries and 1D IETs

## Key Mathematical Insights

### Piecewise Isometries

A map f : α → α that:
- Partitions the space into measurable pieces
- Acts as an isometry on each piece
- May have discontinuities at boundaries

**Unifying framework:** Both IETs and compound symmetry groups are special cases.

### The Critical Transition

**Below r_crit:** All orbits are periodic (finite group)
**At r_crit:** Infinite orbits first appear
**Above r_crit:** Complex dynamics (unbounded orbits possible)

**The mechanism:** At r_crit, a line segment is invariant under the group action and exhibits IET dynamics with irrational parameters → infinite orbit.

### Dimensional Reduction

**Key insight of Theorem 2:** The 2D system reduces to a 1D IET at the critical point.

- 2D compound symmetry group acting on ℝ²
- At r_crit, segment E'E is invariant
- First return map to segment is a 3-interval IET
- IET has golden ratio structure → infinite orbit

This dimensional reduction is what makes the proof tractable.

## Development Guidelines

### Code Quality
- Follow Mathlib style conventions
- Document all public definitions
- Explain proof strategies in comments
- Use `sorry` strategically with TODO comments

### Testing Protocol
- Every change: `./check_lean.sh --errors-only`
- Before commit: `./check_lean.sh --transparency`
- Project-wide: `./check_lean.sh --all errors-only TDCSG/`

### Git Workflow
- Atomic commits (one logical change)
- Descriptive commit messages
- Never commit failing transparency checks
- Clean `git status` (no scratch files)

## References

**Primary Source:**
- Hearn, Kretschmer, Rokicki, Streeter, Vergo (2023). *Two-Disk Compound Symmetry Groups*. [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)

**IET Theory:**
- Keane (1975). *Interval Exchange Transformations*
- Masur (1982). *Interval exchange transformations and measured foliations*
- Veech (1982). *Gauss measures for transformations on IETs*

**Mathlib:**
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- Especially: Geometry.Euclidean, GroupTheory.GroupAction, Dynamics

## License

Apache 2.0 - See LICENSE file

---

**Current Phase:** Scaffolding complete, ready for proof development
**Next Milestone:** Complete TwoDisk.lean (11 sorries)
**End Goal:** Theorem 2 fully proven with 0 sorries
