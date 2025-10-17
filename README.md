# TDCSG - Piecewise Isometries Formalization

Formal verification of topological dynamical systems with a focus on piecewise isometries in Lean 4.

## Current Status (2025-10-17)

**Build Status:** ✅ All 8 files compile with zero errors
**Remaining Sorries:** 9 across 3 files
**Completion:** 5/8 files fully proven (0 sorries)

### Files by Status

**Complete (0 sorries):**
- **Basic.lean** - Core `PiecewiseIsometry` structure definition
- **Properties.lean** - Basic properties and lemmas
- **MeasurePreserving.lean** - Measure-theoretic properties
- **Composition.lean** - Category structure and composition
- **Finite.lean** - Finite partition specializations

**In Progress:**
- **IntervalExchange.lean** - 1 sorry (interval injectivity lemma)
- **Examples.lean** - 4 sorries (IET-dependent examples)
- **Ergodic.lean** - 4 sorries (research-level theorems)

## Quick Start

### Check Build Status
```bash
# Verify all files compile
./check_lean.sh --all errors-only TDCSG/

# Show sorry summary
./check_lean.sh --all sorries TDCSG/

# Check specific file
./check_lean.sh --errors-only TDCSG/Basic.lean
```

### Build Tools

The project uses `./check_lean.sh` for efficient build verification:

| Mode | Command | Purpose |
|------|---------|---------|
| `--errors-only` | Single file errors | Fast compilation check |
| `--sorries` | Sorry tracking | See theorem names & locations |
| `--warnings-summary` | Warning analysis | Categorized warnings |
| `--all <mode>` | Multi-file check | Aggregate results |

**Documentation:** [tools/CHECK_LEAN_TOOL.md](tools/CHECK_LEAN_TOOL.md)

**Key Features:**
- 99% token reduction vs raw `lake build`
- Complete diagnostics (never clips messages)
- Per-file filtering
- Multi-file aggregation

## Sorry Breakdown

### IntervalExchange.lean (1 sorry)

**Line 559: `interval_injective`**
- Prove interval function is injective
- Status: Tractable with standard Mathlib tactics

### Examples.lean (4 sorries)

All blocked on IET infrastructure:

| Line | Theorem | Blocker |
|------|---------|---------|
| 198 | `simple_two_IET_discontinuity` | IET partition structure |
| 205 | `simple_two_IET_is_rotation` | `IET.toFun` implementation |
| 332 | `double_rotation_discontinuity` | Partition frontier computation |
| 856 | `two_IET_period_two` | `iterated_two_IET` definition |

### Ergodic.lean (4 sorries)

Research-level theorems:

| Line | Theorem | Classification |
|------|---------|----------------|
| 320 | `ergodic_iff_irreducible` | 1-2 weeks (Poincaré recurrence) |
| 391 | Masur-Veech | **IMPOSSIBLE** (needs Teichmüller theory) |
| 522 | Keane's theorem | 1-2 months (ergodic decomposition) |
| 756 | `ergodic_of_minimal` | 1-2 weeks (70-80% complete) |

## Project Structure

```
TDCSG/
├── check_lean.sh              # Main build verification tool
├── tools/                     # Build tool implementation
│   ├── CHECK_LEAN_TOOL.md    # Tool documentation
│   ├── check_lean_errors_only.py
│   ├── check_lean_file.py
│   ├── check_lean_multi.py
│   ├── check_lean_sorries.py
│   └── check_lean_warnings_summary.py
├── TDCSG/                     # Main formalization
│   ├── Basic.lean            # Core definitions ✅
│   ├── Properties.lean       # Basic lemmas ✅
│   ├── MeasurePreserving.lean # Measure theory ✅
│   ├── Composition.lean      # Composition ✅
│   ├── Finite.lean           # Finite partitions ✅
│   ├── IntervalExchange.lean # IETs (1 sorry)
│   ├── Examples.lean         # Examples (4 sorries)
│   └── Ergodic.lean          # Ergodic theory (4 sorries)
└── README.md                  # This file
```

## Mathematical Background

### Piecewise Isometries

A **piecewise isometry** is a map `f : α → α` on a metric space that:
- Partitions the space into measurable pieces
- Acts as an isometry on each piece
- May have discontinuities at partition boundaries

**Key Properties:**
- Discontinuity set has measure zero
- Preserves distances within each piece
- Natural examples: interval exchange transformations, outer billiards

### Interval Exchange Transformations (IETs)

IETs are piecewise isometries on `[0,1)` that:
- Partition `[0,1)` into finitely many intervals
- Rearrange intervals via permutation
- Translate each interval (preserving lengths)

**Applications:**
- Models for billiards
- Connection to Teichmüller theory
- Ergodic theory examples

## Key Theorems (Proven)

### Basic.lean
- `PiecewiseIsometry` structure definition
- `discontinuitySet_measurable` - discontinuity set is measurable
- `exists_mem_partition` - every point belongs to some partition piece

### Composition.lean
- `comp` - composition of piecewise isometries
- `iterate_finite_discontinuities` - iterations preserve finite discontinuities

### Properties.lean
- `isometry_on` - distance preservation on each piece
- Partition properties (cover, disjoint, nonempty)

## Research Connections

### Ergodic Theory (Ergodic.lean)

**Goal:** Connect topological dynamics (minimality, dense orbits) with measure theory (ergodicity).

**Key Results:**
- Minimal systems → ergodic (Walters, Theorem 6.11)
- Unique ergodicity of generic IETs (Masur-Veech, 1982)
- Keane's theorem (minimality → unique ergodicity)

**Status:** Infrastructure gaps prevent full formalization

### Examples (Examples.lean)

Concrete instances demonstrating theory:
- 2-interval exchanges (rotations)
- Planar rotations
- Period-doubling cascades

**Status:** Blocked on IET infrastructure completion

## Contributing

### Development Workflow

1. **Make changes** to `.lean` files
2. **Verify compilation:**
   ```bash
   ./check_lean.sh --errors-only TDCSG/YourFile.lean
   ```
3. **Check for new sorries:**
   ```bash
   ./check_lean.sh --sorries TDCSG/YourFile.lean
   ```
4. **Review warnings:**
   ```bash
   ./check_lean.sh --warnings-summary TDCSG/YourFile.lean
   ```

### Code Standards

- **No axioms** - all proofs must be constructive
- **Document sorries** - explain why proof is incomplete
- **Follow Mathlib style** - naming, formatting conventions
- **Test after every change** - use `./check_lean.sh`

## Future Work

### Short Term (Achievable)
1. Complete `interval_injective` (IntervalExchange.lean:559)
2. Implement IET infrastructure to unblock Examples.lean
3. Work on `ergodic_of_minimal` final gap (Ergodic.lean:756)

### Long Term (Research Projects)
1. Formalize Poincaré recurrence for Ergodic.lean:320
2. Ergodic decomposition for Keane's theorem
3. (Infeasible) Teichmüller theory for Masur-Veech

## References

### Literature

- Walters, *An Introduction to Ergodic Theory* (1982) - Chapter 6
- Keane, "Interval Exchange Transformations" (1975)
- Masur & Veech, "The Teichmüller geodesic flow" (1982)

### Mathlib Resources

- `Mathlib.MeasureTheory.Measure.Regular` - Regularity properties
- `Mathlib.Dynamics.Ergodic.Ergodic` - Ergodic definitions
- `Mathlib.Dynamics.Minimal` - Minimality
- `Mathlib.Algebra.BigOperators.Fin` - Finite sums

## License

Apache 2.0 - See LICENSE file

## Contact

Eric Moffat - Project maintainer
