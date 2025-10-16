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

## Key Features

### Three-Tiered Structure Pattern

Following mathlib4 best practices (similar to ergodic theory modules):

1. **`PiecewiseIsometry α`** - Base structure
   - Measurable partition of metric space
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

### Core Definitions

```lean
import TDCSG

-- Define a piecewise isometry
def myMap : PiecewiseIsometry ℝ := ...

-- Check discontinuity set
#check myMap.discontinuitySet

-- Compose piecewise isometries
def composed := myMap.comp otherMap

-- Iterate n times
def iterated := PiecewiseIsometry.iterate myMap n
```

### Interval Exchange Transformations

```lean
-- Define a 2-interval exchange (rotation)
def rotation : IntervalExchangeTransformation 2 :=
  IET_two_intervals (1/2) (by norm_num)

-- Convert to piecewise isometry
def rotationPI : PiecewiseIsometry ℝ :=
  rotation.toPiecewiseIsometry

-- Verify measure preservation
example : MeasureTheory.MeasurePreserving rotation.toFun
    (volume.restrict (Ico 0 1)) (volume.restrict (Ico 0 1)) :=
  rotation.preserves_lebesgue
```

## Mathematical Content

### Structures

- `PiecewiseIsometry α` - Core structure with partition and isometry conditions
- `MeasurePreservingPiecewiseIsometry α μ` - Measure-preserving maps
- `ErgodicPiecewiseIsometry α μ` - Ergodic systems
- `FinitePiecewiseIsometry α` - Finite partition specialization
- `IntervalExchangeTransformation n` - IETs with n intervals
- `MinimalPiecewiseIsometry α μ` - Minimal dynamical systems

### Key Theorems (Scaffolded with `sorry`)

- `discontinuitySet_measurable` - Discontinuity sets are measurable
- `measurePreserving_of_null_discontinuities` - Null discontinuity → measure preserving
- `ergodic_of_mixing` - Mixing implies ergodic
- `minimal_implies_uniquely_ergodic` - Minimality → unique ergodicity
- `IET_preserves_lebesgue` - IETs preserve Lebesgue measure
- `two_IET_uniquely_ergodic` - Irrational 2-IETs are uniquely ergodic

### Examples Included

- Identity map and single rotations
- Double rotation on planar regions
- Simple 2-interval and 3-interval exchanges
- Square billiard (simplified model)
- Reflection maps
- Counter-examples (doubling map, baker's map)

## Development Status

**Current Phase**: Complete Scaffolding ✅

- ✅ All core structures defined with correct type signatures
- ✅ Comprehensive API surface (~80+ definitions and theorems)
- ✅ Full documentation with module docstrings
- ✅ Examples and constructors
- ✅ 5/8 modules compile successfully
- 🔄 Remaining: Proof implementation (all theorems use `sorry` placeholders)

### Build Status

```bash
$ lake build
# Core modules (Basic, Properties, Composition) compile successfully
# Minor name collisions in extending structures remain to be resolved
```

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

# Build the project
lake build
```

### Quick Start

```lean
import TDCSG

-- Access all piecewise isometry functionality
open PiecewiseIsometry

-- Define your own piecewise isometry
def myPI : PiecewiseIsometry ℝ :=
  PiecewiseIsometry.id

-- Work with interval exchanges
def myIET : IntervalExchangeTransformation 3 :=
  IET_three_example (1/3) (1/3) (by norm_num) (by norm_num) (by norm_num)
```

## Architecture & Design

### Design Choices

1. **Bundled Structures**: Following mathlib4 patterns for morphisms
2. **Set-Based Partitions**: Using `Set (Set α)` rather than custom partition types
3. **Separate Tiers**: Clean separation of core properties from technical requirements
4. **Extensive Examples**: Demonstrating usage patterns and edge cases

### Mathlib4 Conventions Followed

- ✅ 100-character line limits
- ✅ Proper naming (snake_case for Props, UpperCamelCase for structures)
- ✅ Copyright headers on all files
- ✅ Module docstrings with sections (Main definitions, Main results, Notation, References)
- ✅ Docstrings on definitions and major theorems
- ✅ 2-space proof indents, focusing dots
- ✅ Proper namespace organization

## Contribution Roadmap

### Phase 1: Scaffolding ✅ **COMPLETE**
- Define all structures and theorem statements
- Establish API surface
- Create examples

### Phase 2: Core Proofs 🔄 **NEXT**
- Prove basic properties (partition coverage, disjointness)
- Establish isometry properties
- Implement constructor helpers

### Phase 3: Measure Theory
- Prove measure preservation theorems
- Connect to mathlib's `MeasurePreserving`
- Handle null discontinuity sets

### Phase 4: Ergodic Theory
- Prove ergodicity results
- Implement Birkhoff ergodic theorem applications
- Unique ergodicity for IETs

### Phase 5: Interval Exchanges
- Complete IET theory
- Rauzy induction
- Masur-Veech theorem (if feasible)

### Phase 6: Mathlib PR Preparation
- Remove all `sorry` placeholders
- Comprehensive documentation review
- Community engagement on Zulip
- Submit incremental PRs (~200 lines each)

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

## Technical Notes

### Known Limitations

- Discontinuity set measurability requires countability or finiteness assumptions
- Composition partition refinement is axiomatized (proof TODO)
- Some isometry/distance conversions between `dist` and `edist` need completion
- Name collisions in measure-preserving structures need resolution

### Design Document

See [`piecewise_isometries_architecture_reccomendation.md`](piecewise_isometries_architecture_reccomendation.md) for the complete architectural analysis and design rationale.

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

**Status**: Active Development | **Version**: 0.1.0 (Scaffolding Phase) | **Last Updated**: October 2024
