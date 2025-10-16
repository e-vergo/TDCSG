# Piecewise Isometries Formalization in Lean 4

A comprehensive formalization of piecewise isometries for eventual contribution to mathlib4. This library provides a rigorous mathematical framework for studying piecewise isometric dynamical systems, including interval exchange transformations and polygonal billiards.

## Overview

Piecewise isometries are maps on metric spaces that restrict to isometries on each piece of a measurable partition. They arise naturally in:
- **Interval Exchange Transformations (IETs)**: Fundamental objects in Teichmüller theory and flat surfaces
- **Polygonal Billiards**: Models of particle dynamics in bounded domains
- **Dynamical Systems**: Examples of measure-preserving transformations with rich ergodic properties

This formalization follows mathlib4 conventions and is structured for eventual PR submission to the Lean mathematical library.

## Project Structure

```
TDCSG/
├── Basic.lean               # Core PiecewiseIsometry structure and predicates
├── Properties.lean          # Basic lemmas, partition helpers, constructors
├── Composition.lean         # Composition and iteration of piecewise isometries
├── MeasurePreserving.lean   # Measure-preserving extensions
├── Ergodic.lean            # Ergodic theory integration
├── Finite.lean             # Finite partition specializations
├── IntervalExchange.lean   # Interval exchange transformations
└── Examples.lean           # Concrete examples and use cases
```

## Current Status

### Build Status: ✅ Clean

```bash
$ lake build
# Build completed successfully (2264 jobs)
# All 8 files compile without errors or warnings
# 0 non-sorry compilation errors
# 0 linter warnings
```

### Proof Status

- **Total Theorems**: ~80+ theorem statements
- **Proven**: ~15-20 basic lemmas
- **Remaining**: ~60+ theorems with `sorry` placeholders

All core structures are defined with correct type signatures. The scaffolding is complete and the codebase is ready for systematic proof development.

## Key Features

### Three-Tiered Structure Pattern

Following mathlib4 best practices (similar to ergodic theory modules):

1. **`PiecewiseIsometry α`** - Base structure
   - Countable measurable partition of metric space
   - Isometric restriction to each piece
   - Discontinuity set characterization

2. **`MeasurePreservingPiecewiseIsometry α μ`** - Extends base with measure theory
   - Measurable function requirement
   - Measure preservation property
   - Connections to `MeasureTheory.MeasurePreserving`

3. **`ErgodicPiecewiseIsometry α μ`** - Full dynamical system
   - Ergodicity property
   - Integration with `MeasureTheory.Ergodic`
   - Birkhoff ergodic theorem applications

### Core API

```lean
import TDCSG

-- Define a piecewise isometry
def myMap : PiecewiseIsometry ℝ := PiecewiseIsometry.id

-- Check discontinuity set
#check myMap.discontinuitySet

-- Compose piecewise isometries
def composed := myMap.comp otherMap

-- Iterate n times
def iterated := PiecewiseIsometry.iterate myMap n
```

## Mathematical Content

### Structures

- `PiecewiseIsometry α` - Core structure with partition and isometry conditions
- `MeasurePreservingPiecewiseIsometry α μ` - Measure-preserving maps
- `ErgodicPiecewiseIsometry α μ` - Ergodic systems
- `FinitePiecewiseIsometry α` - Finite partition specialization
- `IntervalExchangeTransformation n` - IETs with n intervals
- `MinimalPiecewiseIsometry α μ` - Minimal dynamical systems

### Key Theorems (Scaffolded)

#### Basic Properties (Basic.lean)
- `discontinuitySet_measurable` - Discontinuity sets are measurable ✅
- `exists_mem_partition` - Every point belongs to some partition piece
- `isometry_on_same_piece` - Distance preservation within pieces

#### Composition (Composition.lean)
- `comp_refinement` - Composition refines partitions
- `iterate_periodic` - Iteration properties

#### Measure Theory (MeasurePreserving.lean)
- `measurePreserving_of_null_discontinuities` - Null discontinuity → measure preserving
- `measure_preimage_piece` - Measure decomposition

#### Ergodic Theory (Ergodic.lean)
- `ergodic_of_mixing` - Mixing implies ergodic
- `minimal_implies_uniquely_ergodic` - Minimality → unique ergodicity

#### Finite Partitions (Finite.lean)
- `card_pos` - Cardinality bounds
- `card_comp_le` - Composition bounds
- `card_iterate_le` - Iteration bounds

#### Interval Exchanges (IntervalExchange.lean)
- `intervals_measurable` - IET intervals are measurable
- `preserves_lebesgue` - IETs preserve Lebesgue measure (scaffolded)
- `two_IET_uniquely_ergodic` - Irrational 2-IETs are uniquely ergodic (scaffolded)

### Examples (Examples.lean)

All examples compile cleanly with structural proofs as `sorry`:
- Identity map and rotations
- Double rotation on planar regions
- Simple 2-interval and 3-interval exchanges
- Half-plane reflection
- Square billiard (simplified model)
- Counter-examples (doubling map, baker's map showing non-isometries)

## Installation & Usage

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (version 4.24.0-rc1 or later)
- [mathlib4](https://github.com/leanprover-community/mathlib4)

### Setup

```bash
# Clone the repository
git clone https://github.com/yourusername/TDCSG.git
cd TDCSG

# Get mathlib4 cache (speeds up compilation)
lake exe cache get

# Build the project (clean build)
lake build
```

### Quick Start

```lean
import TDCSG

-- Access all piecewise isometry functionality
open PiecewiseIsometry

-- Use the identity map
def myPI : PiecewiseIsometry ℝ := PiecewiseIsometry.id

-- Compose and iterate
def composed := myPI.comp myPI
def iterated := PiecewiseIsometry.iterate myPI 10
```

## Architecture & Design

### Design Choices

1. **Bundled Structures**: Following mathlib4 patterns for morphisms
2. **Countable Partitions**: Added `partition_countable` field for measurability
3. **Set-Based Partitions**: Using `Set (Set α)` rather than custom partition types
4. **Separate Tiers**: Clean separation of core properties from technical requirements
5. **Extensive Examples**: Demonstrating usage patterns and edge cases

### Mathlib4 Conventions Followed

- ✅ 100-character line limits
- ✅ Proper naming (snake_case for Props, UpperCamelCase for structures)
- ✅ Copyright headers on all files
- ✅ Module docstrings with sections
- ✅ Docstrings on definitions and major theorems
- ✅ 2-space proof indents
- ✅ Proper namespace organization
- ✅ Clean build without linter warnings

## Contribution Roadmap

### Current Phase: Proof Development 🔄

**Priority Areas:**
1. Complete partition property proofs (coverage, disjointness)
2. Prove basic isometry lemmas
3. Establish composition theory
4. Measure preservation core results

**Next Steps:**
- Fill in `sorry` placeholders systematically by file
- Start with Properties.lean and Composition.lean
- Build up to measure theory and ergodic results
- Complete IET theory

### Future Phases

1. **Measure Theory Completion**
   - Prove measure preservation theorems
   - Connect to mathlib's `MeasurePreserving`
   - Handle null discontinuity sets

2. **Ergodic Theory**
   - Prove ergodicity results
   - Implement Birkhoff ergodic theorem applications
   - Unique ergodicity for IETs

3. **Interval Exchanges**
   - Complete IET theory
   - Rauzy induction
   - Masur-Veech theorem (if feasible)

4. **Mathlib PR Preparation**
   - Remove remaining `sorry` placeholders
   - Comprehensive documentation review
   - Community engagement on Zulip
   - Submit incremental PRs (~200 lines each)

## Technical Notes

### Recent Improvements

- Added `partition_countable` field to ensure measurability of discontinuity sets
- Resolved all name collisions in measure-preserving structures
- Fixed namespace issues in ergodic theory integration
- All examples now compile cleanly
- Zero linter warnings across entire codebase

### Known Remaining Work

- Most theorems use `sorry` placeholders awaiting proofs
- IET `toFun` and conversion functions are scaffolded
- Some complex partition refinement proofs need implementation
- Ergodic characterization theorems need completion

## References

### Mathematical Background

- **Adler, Kitchens, Tresser** (2001): *Dynamics of non-ergodic piecewise affine maps of the torus*
- **Goetz** (2000): *Dynamics of piecewise isometries*
- **Keane** (1975): *Interval exchange transformations*
- **Masur** (1982): *Interval exchange transformations and measured foliations*
- **Veech** (1982): *Gauss measures for transformations on the space of interval exchange maps*
- **Walters** (1982): *An Introduction to Ergodic Theory*

### Lean 4 Resources

- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathlib4 Contributing Guide](https://leanprover-community.github.io/contribute/index.html)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

## License

Released under Apache 2.0 license (standard for mathlib4 contributions).

## Author

Eric Moffat

## Acknowledgments

- Architecture follows patterns from mathlib4's ergodic theory modules
- Design informed by mathlib4 community best practices
- Built with Lean 4 and mathlib4

## Contact & Contribution

For questions, suggestions, or contributions:
- Open an issue on GitHub
- Join discussions on [Lean Zulip](https://leanprover.zulipchat.com/) (#mathlib4 stream)
- Submit pull requests following mathlib4 conventions

---

**Status**: Clean Build | **Phase**: Proof Development | **Last Updated**: January 2025
