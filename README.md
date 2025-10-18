# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Goal:** Formalize Theorem 2 - proving that GG₅ has critical radius r_c = √(3 + φ) via emergence of a 3-interval exchange transformation.

## Current Status

**Build:** ❌ 15/16 files compile (SegmentMaps.lean has errors)
**Sorries:** 28 sorries across 5 files (11 files proof-complete)
**Phase:** Theorem 2 completion - second parallel agent session attempted (2025-10-18)

**Progress Summary:**
- Overall: 50% sorry reduction from original 56 sorries
- Session 1 (earlier 2025-10-18): 30 sorries eliminated ✅
- Session 2 (current): Net +2 sorries (regression)
- Critical blocker: SegmentMaps.lean broke during session 2

## ⚠️ Latest Agent Session Results (2025-10-18, Session 2)

**Deployment:** 5 agents launched in parallel (one per file with sorries)
**Result:** Limited progress - 2 sorries eliminated, net +2 due to SegmentMaps regression

### Per-File Results (Session 2)

**❌ [Geometry.lean](TDCSG/CompoundSymmetry/GG5/Geometry.lean) - No Progress**
- 9 → 9 sorries (unchanged)
- Agent analysis: Requires complex trigonometric calculations with 5th roots of unity
- Added import and documentation, but no sorries eliminated
- Mathematical difficulty exceeded agent capabilities

**❌ [SegmentMaps.lean](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean) - REGRESSION**
- 6 → 10 sorries (+4 helper lemmas added)
- **CRITICAL: File now has 8 compilation errors**
- Agent added incomplete helper lemmas that broke the build
- Violates completion criteria (must compile cleanly)

**✅ [TwoDisk.lean](TDCSG/CompoundSymmetry/TwoDisk.lean) - Partial Success**
- 6 → 4 sorries (2 eliminated)
- **Proven:** `basicPartition_measurable`, `basicPartition_cover`
- **Architectural blocker documented:** `basicPartition_disjoint` is mathematically false (overlapping disks)
- Remaining 3 sorries: EuclideanSpace type class issues

**❌ [Finiteness.lean](TDCSG/CompoundSymmetry/Finiteness.lean) - Architectural Blocker**
- 1 → 1 sorry (unchanged)
- Agent determination: Unprovable without compound symmetry group infrastructure
- Theorem requires axioms not yet formalized

**❌ [Ergodic.lean](TDCSG/Ergodic.lean) - Research-Level Blockers Confirmed**
- 4 → 4 sorries (unchanged)
- Sorry #2 (Masur-Veech): Agent confirms impossible with current Mathlib (2-5 years)
- Other sorries require significant infrastructure (weeks to months)
- Comprehensive analysis completed, no path forward without major infrastructure

### Quality Verification (Session 2)

❌ Build status: 15/16 files compile (SegmentMaps.lean broken)
✅ Transparency checks: All files pass (no axioms, no placeholder proofs)
✅ File modifications: All 5 files modified (git verified)
❌ Net progress: +2 sorries (26 → 28)

### Root Cause Analysis

The agents encountered **genuine mathematical difficulty**:
- Complex analysis (cyclotomic polynomials, trigonometric identities)
- Broken implementation (SegmentMaps helper lemmas don't compile)
- Architectural issues (overlapping disks, missing infrastructure)
- Research-level mathematics (Masur-Veech theorem from 1982)

## ✅ Previous Session Results (2025-10-18, Session 1)

**Deployment:** 6 agents launched in parallel (one per file with sorries)
**Result:** Major success - 30 sorries eliminated, 54% reduction

### Per-File Results (Session 1)

**🎉 [IET.lean](TDCSG/CompoundSymmetry/GG5/IET.lean) - COMPLETE!**
- 14 → 0 sorries (100% complete)
- All algebraic IET infrastructure proven
- Key achievements:
  - ✅ Positivity proofs (3 interval lengths)
  - ✅ Golden ratio multiplication identities
  - ✅ Lengths sum to one
  - ✅ IET structure validation
  - ✅ Emergent IET theorems

**🚀 [Geometry.lean](TDCSG/CompoundSymmetry/GG5/Geometry.lean) - Major Progress**
- 12 → 9 sorries (3 eliminated, 25% reduction)
- **CRITICAL:** ✅ `cos_two_pi_fifth` proven (key blocker eliminated!)
- Removed 3 transparency violations (placeholder theorems)
- Path forward clear for remaining 9 sorries

**📐 [SegmentMaps.lean](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean) - Honest Cleanup**
- 14 → 6 sorries (8 eliminated, 57% reduction)
- Deleted 8 false isometry lemmas (mathematically unprovable)
- Remaining 6 sorries blocked on Geometry.lean completion

**⚠️ [TwoDisk.lean](TDCSG/CompoundSymmetry/TwoDisk.lean) - Partial Progress**
- 11 → 6 sorries (5 eliminated)
- Blocker confirmed: Overlapping disks violate partition disjointness
- Design decision required

**🔬 [Finiteness.lean](TDCSG/CompoundSymmetry/Finiteness.lean) - Unprovable as Stated**
- 1 → 1 sorry (theorem requires additional axioms)
- Awaiting fuller compound symmetry group formalization

**📚 [Ergodic.lean](TDCSG/Ergodic.lean) - Research-Level Blockers**
- 4 → 4 sorries (comprehensive blocker escalation completed)
- Sorry #2 (Masur-Veech): Impossible with current Mathlib (2-5 years)
- Sorries #1, #4: Provable in 1-2 weeks each with infrastructure
- Sorry #3: Provable in 1-2 months with ergodic decomposition

### Quality Verification (Session 1)

✅ All 16 files compile without errors
✅ All modified files pass transparency checks
✅ Zero custom axioms introduced
✅ All file modifications persisted (git verified)
✅ 100% Anti-Placeholder Protocol compliance

### Proof-Complete Files (11/16 files, 0 sorries)
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
- `TDCSG.CompoundSymmetry.GG5.IET` - ✅ **COMPLETE (was 14 sorries, now 0)** 🎉

### Files with Strategic Sorries (5 files, 28 total sorries)

**GG5 Theorem 2 Infrastructure (19 sorries):**
- `Geometry.lean` - 9 sorries (**↓ from 12** in session 1, unchanged in session 2)
  - ✅ **UNBLOCKED:** `cos(2π/5) = (goldenRatio - 1) / 2` proven (session 1)
  - Path forward: Complex norm calculations, segment containment, golden ratio properties
  - Mathematical difficulty: Cyclotomic polynomial calculations exceed current agent capability
- `SegmentMaps.lean` - 10 sorries (**↓ from 14** in session 1, **↑ from 6** in session 2)
  - ❌ **BROKEN:** File has 8 compilation errors from incomplete helper lemmas
  - **Immediate action required:** Fix or remove broken lemmas to restore compilation
  - **Blocked on:** Geometry.lean completion (needs geometric positions of E, F, G)

**Two-Disk System (4 sorries):**
- `TwoDisk.lean` - 4 sorries (**↓ from 11** in session 1, **↓ from 6** in session 2)
  - ✅ **Progress:** 2 additional sorries eliminated in session 2
  - **BLOCKER:** `basicPartition_disjoint` is mathematically false (overlapping disks violate disjointness)
  - **Design decision required:** Choose partition refinement approach (see §260-289 below)
  - Remaining 3 sorries: EuclideanSpace type class issues (provable but technical)

**Other (5 sorries, not on Theorem 2 critical path):**
- `Finiteness.lean` - 1 sorry (requires compound symmetry axioms not yet formalized)
- `Ergodic.lean` - 4 sorries (research-level, comprehensive blocker documentation complete)

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

### ✅ Priority 2: GG5 Geometry & IET - MAJOR PROGRESS

**Completed (2025-10-18):**
- ✅ IET.lean - **COMPLETE** (14 → 0 sorries)
- ✅ `cos_two_pi_fifth` - **PROVEN** (critical blocker eliminated!)
- ✅ `zeta5_abs`, `zeta5_ne_one`, `r_crit_approx` - All proven
- ✅ 3 transparency violations removed from Geometry.lean

**Current state:**
- Geometry.lean: 9 sorries remaining (down from 15)
- SegmentMaps.lean: 6 sorries remaining (down from 14)
- **Path to Theorem 2 is now clear!**

### Priority 3: Complete Theorem 2 - NOW UNBLOCKED ✅

**Status:** Critical blocker eliminated, ready for final push

**Remaining work:** 16 sorries blocking Theorem 2
- Geometry.lean: 9 sorries
- SegmentMaps.lean: 6 sorries
- Main theorem: 1 sorry

**Key achievement:** `cos_two_pi_fifth` lemma proven in Geometry.lean
- This was the "CRITICAL BLOCKER" that blocked ~10 downstream sorries
- Now enables complex norm calculations for points E, F, G
- Path forward documented in Theorem 2 Completion Roadmap below

## Theorem 2 Completion Roadmap

**Goal:** Prove `GG5_infinite_at_critical_radius` - that GG₅ is infinite at r = √(3 + φ)

**Current completion:** ~43% (10 of 26 sorries in GG5 files are complete)

**Remaining sorries:** 15 total (9 in Geometry.lean + 6 in SegmentMaps.lean)

### Dependency Chain

```
Geometry.lean (9 sorries)
    ↓ geometric properties of E, F, G
SegmentMaps.lean (6 sorries)
    ↓ three bijections + isometries
segment_maps_imply_infinite_orbit
    ↓ infinite orbit exists
GG5_infinite_at_critical_radius ✓
```

### Phase 1: Complete Geometry.lean (9 sorries → 0)

**Estimated time:** 15-25 hours total

**Status:** ✅ UNBLOCKED (`cos_two_pi_fifth` proven!)

#### Group A: Complex Norm Calculations (2 sorries, 3-5 hours)

**1. `E_on_right_disk_boundary` [line 238](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L238)**
- Prove `‖E - 1‖ = r_crit` where E = ζ₅ - ζ₅²
- Use `cos_two_pi_fifth` to compute ‖E - 1‖²
- Expand using Euler's formula, simplify to 3 + φ

**2. `E_in_left_disk` [line 242](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L242)**
- Prove `‖E - (-1)‖ ≤ r_crit`
- Similar complex norm calculation

#### Group B: Segment Containment (2 sorries, 4-6 hours)

**3. `F_on_segment_E'E` [line 246](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L246)**
- Show F = t·E + (1-t)·E' for some t ∈ [0,1]
- Algebraic manipulation with cyclotomic identities

**4. `G_on_segment_E'E` [line 250](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L250)**
- Use G = 2F - E definition
- Derive from result 3

#### Group C: Ordering and Ratios (2 sorries, 5-8 hours)

**5. `segment_ordering` [line 254](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L254)**
- Establish E' < F < G < E along segment
- Use parameter values from Groups A-B

**6. `segment_ratio_is_golden` [line 273](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L273)**
- Prove segment length ratios involve φ
- Use `Real.goldenRatio_sq` lemma

#### Group D: Irrationality and Containment (3 sorries, 3-6 hours)

**7. `translations_irrational` [line 277](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L277)**
- Show translation lengths are irrational
- Use `Real.goldenRatio_irrational`

**8. `segment_in_disk_intersection` [line 302](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L302)**
- Segment E'E ⊆ leftDisk ∩ rightDisk
- Parameterize segment, check endpoints + continuity

**9. `GG5_infinite_at_critical_radius` [line 345](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L345)**
- Final assembly (depends on Phase 2 completion)

**Tools:** Python verification, computer algebra, cyclotomic polynomial properties

### Phase 2: Complete SegmentMaps.lean (6 sorries → 0)

**Estimated time:** 10-15 hours total

**Prerequisites:** Phase 1 complete

#### Group A: Three Bijections (3 sorries, 6-9 hours)

**1. `map1_bijection_E'F_to_GF` [line 172](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean#L172)**
- Prove a⁻²b⁻¹a⁻¹b⁻¹ maps E'F → GF bijectively
- Use geometric properties from Phase 1

**2. `map2_bijection_FpG_to_FE` [line 195](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean#L195)**
- Prove abab² maps F'G → FE

**3. `map3_bijection_GpE_to_E'G` [line 212](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean#L212)**
- Prove abab⁻¹a⁻¹b⁻¹ maps G'E → E'G

#### Group B: Isometry and Irrationality (2 sorries, 3-4 hours)

**4. `maps_are_isometries_on_intersection` [line 230](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean#L230)**
- Rotations preserve distances on disk intersection
- Use `segment_in_disk_intersection` from Phase 1

**5. `translation_lengths_irrational` [line 250](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean#L250)**
- Direct from `translations_irrational` (Phase 1)

#### Group C: Main Infiniteness Result (1 sorry, 2-3 hours)

**6. `segment_maps_imply_infinite_orbit` [line 279](TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean#L279)**
- Prove orbit grows unboundedly
- Use IET correspondence (IET.lean complete!)
- Irrational translation → dense orbit → unbounded

### Phase 3: Final Assembly

**Time:** 2-3 hours

**Task:** Prove `GG5_infinite_at_critical_radius` [line 345](TDCSG/CompoundSymmetry/GG5/Geometry.lean#L345)
- Connect to `segment_maps_imply_infinite_orbit`
- Verify all hypotheses satisfied

### Total Effort Estimate

- **Phase 1:** 15-25 hours
- **Phase 2:** 10-15 hours
- **Phase 3:** 2-3 hours
- **Total:** 27-43 hours (3-5 full work days)

### Success Criteria

✅ All 15 sorries eliminated (Geometry.lean + SegmentMaps.lean)
✅ All files compile without errors
✅ All transparency checks pass
✅ Zero custom axioms
✅ Mathlib-quality proofs
✅ Theorem 2 proven: GG₅ is infinite at r_c = √(3 + φ)

### Separate Track: TwoDisk.lean (6 sorries)

**Status:** 3 sorries provable but intentionally not completed during session (see agent blocker report)
**Note:** 1 sorry (`basicPartition_disjoint`) blocked by overlapping disk design flaw (see §242-291)
**Not on critical path for Theorem 2**

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

**Current Phase:** Theorem 2 completion push (43% complete, 15 sorries remaining)
**Next Milestone:** Complete Geometry.lean (9 sorries, critical blocker eliminated!)
**End Goal:** Theorem 2 fully proven - GG₅ is infinite at r_c = √(3 + φ)

**Session Summary (2025-10-18):**
- 30 sorries eliminated (54% reduction)
- IET.lean complete (14 → 0 sorries)
- Critical blocker `cos_two_pi_fifth` proven
- Clear roadmap to Theorem 2 (27-43 hours estimated)
