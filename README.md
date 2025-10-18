# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Goal:** Formalize Theorem 2 - proving that GG₅ has critical radius r_c = √(3 + φ) via emergence of a 3-interval exchange transformation.

## Current Status

**Build:** ✅ 16/16 files compile without errors
**Sorries:** 56 strategic sorries across 6 files (10 files proof-complete)
**Phase:** Active proof development - 3 sorries eliminated (2025-10-18)

**✅ Recent Progress (2025-10-18):**
- **Geometry.lean:** Eliminated 3 sorries via parallel agent deployment
  - ✅ `zeta5_abs` - Proved ‖ζ₅‖ = 1 using `Complex.norm_exp_ofReal_mul_I`
  - ✅ `zeta5_ne_one` - Proved ζ₅ ≠ 1 via modular arithmetic contradiction
  - ✅ `r_crit_approx` - Proved numerical bounds using polynomial inequalities
- **Key Blocker Identified:** Need `cos(2π/5) = (goldenRatio - 1) / 2`
  - Mathlib HAS: `Real.cos_pi_div_five : cos(π/5) = (1 + √5) / 4`
  - Path forward: Derive cos(2π/5) using `Real.cos_two_mul` (double-angle formula)
  - This will unblock ~10 remaining Geometry.lean sorries

**⚠️ Previous Agent Orchestration Incident (2025-10-17):**
- Attempted parallel agent deployment to eliminate all sorries
- **Result:** FAILED - Zero sorries eliminated (agent edits didn't persist)
- **Fix:** Updated directive with file persistence verification protocol
- **2025-10-18 Success:** New verification protocol works - parallel agents eliminated 3 sorries

### Proof-Complete Files (10/16 files, 0 sorries)
- `TDCSG.Basic` - Piecewise isometry framework
- `TDCSG.Composition` - Composition and iteration
- `TDCSG.Finite` - Finite partition specializations
- `TDCSG.IntervalExchange` - IET infrastructure (critical for Theorem 2)
- `TDCSG.MeasurePreserving` - Measure-preserving transformations
- `TDCSG.Properties` - Partition and isometry lemmas
- `TDCSG.Examples` - Proven examples and counterexamples
- `TDCSG.Planar.Disks` - ✅ COMPLETE (was 3 sorries, now 0)
- `TDCSG.Planar.Rotations` - ✅ COMPLETE (was 2 sorries, now 0)
- `TDCSG.CompoundSymmetry.GG5.CriticalRadius` - ✅ COMPLETE (was 2 sorries, now 0)

### Files with Strategic Sorries (6 files, 56 total sorries)

**GG5 Theorem Infrastructure (40 sorries):**
- `Geometry.lean` - 12 sorries (**↓ from 15**, eliminated 3 on 2025-10-18)
  - **BLOCKER:** Need `cos(2π/5) = (goldenRatio - 1) / 2` to unlock ~10 more
- `IET.lean` - 14 sorries (interval exchange emergence proof)
- `SegmentMaps.lean` - 14 sorries (bijections and isometries)

**Two-Disk System (11 sorries):**
- `TwoDisk.lean` - 11 sorries (partition properties, generator isometries)
  - **BLOCKER:** Design flaw with overlapping disks (see README §186-236)

**Other (5 sorries):**
- `Finiteness.lean` - 1 sorry (Theorem 1 statement)
- `Ergodic.lean` - 4 sorries (research-level, not imported in main)

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

## Next Steps: Proof Development Plan (Updated 2025-10-18)

### ⚠️ BLOCKER: TwoDisk.lean Design Flaw (Discovered 2025-10-17)

**CRITICAL ISSUE:** The current `basicPartition` definition is **mathematically invalid** when disks overlap.

**The Problem:**
```lean
def basicPartition := {leftDisk, rightDisk, exterior}
```

When `dist leftCenter rightCenter ≤ r1 + r2` (overlapping or touching disks):
- `leftDisk ∩ rightDisk ≠ ∅` (non-empty intersection)
- Violates `PiecewiseIsometry.partition_disjoint` requirement
- **Cannot prove `basicPartition_disjoint`** (it's false!)

**Why this matters:** The two-disk compound symmetry groups in the paper have **overlapping disks** at the critical radius. The current formalization cannot handle this.

**Required Decision (Choose One):**

**Option 1: Refined Partition (Recommended)**
```lean
def basicPartition := {
  leftDisk \ rightDisk,     -- left-only region
  leftDisk ∩ rightDisk,     -- overlap region (need priority rule)
  rightDisk \ leftDisk,     -- right-only region
  exterior                  -- outside both
}
```
- **Pros:** Handles overlapping disks (matches paper)
- **Cons:** Need to specify which generator applies in overlap
- **Paper guidance needed:** Does left disk have priority? Or define map differently on overlap?

**Option 2: Disjointness Constraint**
```lean
structure TwoDiskSystem where
  ...
  disks_disjoint : dist leftCenter rightCenter > r1 + r2
```
- **Pros:** Makes current code work immediately
- **Cons:** Excludes the interesting GG5 case (critical radius has touching disks!)

**Option 3: Open Balls**
```lean
leftDisk := Metric.ball (leftCenter sys) sys.r1  -- open ball
```
- **Pros:** Open balls that touch are disjoint
- **Cons:** Creates measure-zero gaps at boundaries, changes semantics

**Recommendation:** Review paper §2-3 to determine intended behavior on overlap region, then implement Option 1 with appropriate precedence rule.

**Impact:** TwoDisk.lean **BLOCKED** until design decision made. Cannot reach 0 sorries with current definition.

---

### ✅ Priority 1: Planar Geometry & CriticalRadius - COMPLETE

**Status:** All 7 sorries in Disks.lean, Rotations.lean, and CriticalRadius.lean have been eliminated.
- These files were already complete when session began (outdated README)
- Verified with `./check_lean.sh --sorries` showing 0 sorries for all three files

### ✅ Priority 2: GG5 Geometry - 5th Root Basics - COMPLETE

**Recently completed (2025-10-18):**
- ✅ `zeta5_abs` - Proved ‖ζ₅‖ = 1
- ✅ `zeta5_ne_one` - Proved ζ₅ ≠ 1
- ✅ `r_crit_approx` - Proved numerical bounds

**Remaining in Geometry.lean:** 12 sorries (down from 15)

### Priority 3: GG5 Geometry - Cyclotomic Blocker (12 sorries) - ACTION REQUIRED

**CRITICAL BLOCKER IDENTIFIED (2025-10-18):**

The key missing lemma that blocks ~10 of the 12 remaining Geometry.lean sorries:

```lean
lemma cos_two_pi_fifth : Real.cos (2 * π / 5) = (Real.goldenRatio - 1) / 2
```

**GOOD NEWS - Mathlib HAS the foundation:**
- ✅ `Real.cos_pi_div_five : cos(π/5) = (1 + √5) / 4` **exists in Mathlib**
- ✅ `Real.cos_two_mul : cos(2x) = 2·cos²(x) - 1` **exists in Mathlib**
- ✅ `Real.goldenRatio : (1 + √5) / 2` **exists in Mathlib**

**DERIVATION PATH (proven feasible):**
```lean
-- Step 1: Apply double-angle formula
cos(2π/5) = 2·cos²(π/5) - 1

-- Step 2: Substitute Mathlib's cos_pi_div_five
         = 2·((1 + √5) / 4)² - 1

-- Step 3: Algebraic simplification
         = 2·(1 + 2√5 + 5) / 16 - 1
         = (6 + 2√5) / 8 - 1
         = (2√5 - 2) / 8
         = (√5 - 1) / 4

-- Step 4: Relate to golden ratio
         = (goldenRatio - 1) / 2
```

**Estimated effort:** 20-50 lines of Lean code, 1-2 hours

**Once proven, this unblocks:**
1. `E_on_right_disk_boundary` - Computing ‖E - 1‖ = r_crit
2. `E_in_left_disk` - Norm bound verification
3. `F_on_segment_E'E` - Segment containment
4. `G_on_segment_E'E` - Segment containment
5. `segment_ordering` - Point ordering along segment
6. `segment_ratio_is_golden` - Golden ratio relationships
7. `translations_irrational` - Irrationality proof
8. `segment_in_disk_intersection` - Geometric bounds
9. And potentially 2-3 more via cascading dependencies

**Next action:** Prove `cos_two_pi_fifth` using double-angle formula approach.

### Priority 4: Segment Maps & IET (28 sorries) - Depends on Priority 3

**SegmentMaps.lean (14 sorries):**
- Prove the three bijections: E'F→GF, FG→FE, GE→E'G
- Show they are isometries
- Prove irrational translation lengths
- **Blocker:** Requires Geometry.lean completion (especially cos(2π/5) lemma)

**IET.lean (14 sorries):**
- Show interval lengths are positive
- Prove they sum to 1
- Establish golden ratio relationships
- Connect segment dynamics to IET structure
- **Blocker:** Requires both Geometry.lean and SegmentMaps.lean

**Why:** This is the core of Theorem 2 - the IET emergence

**Strategy:**
1. First complete Priority 3 (prove cos(2π/5) and Geometry.lean)
2. Then SegmentMaps.lean becomes tractable
3. Finally IET.lean assembles everything into Theorem 2

### Priority 5: TwoDisk.lean (11 sorries) - BLOCKED (see §197-246)

**Status:** Requires design decision on overlapping disk handling before any proofs can proceed.

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
