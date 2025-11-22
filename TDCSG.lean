-- Core 1D piecewise isometry framework
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Composition
import TDCSG.MeasurePreserving
import TDCSG.Finite
import TDCSG.IntervalExchange
import TDCSG.Examples

-- 2D planar geometry infrastructure
import TDCSG.Planar.Rotations
import TDCSG.Planar.Disks

-- Two-disk compound symmetry groups
import TDCSG.CompoundSymmetry.TwoDisk
import TDCSG.CompoundSymmetry.Finiteness

-- Theorem 2: GG₅ critical radius formalization
import TDCSG.CompoundSymmetry.GG5.Geometry
import TDCSG.CompoundSymmetry.GG5.SegmentMaps.Main
import TDCSG.CompoundSymmetry.GG5.IET
import TDCSG.CompoundSymmetry.GG5.CriticalRadius

/-!
# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification of **Two-Disk Compound Symmetry Groups** from [arXiv:2302.12950v1].

**Primary Goal:** Formalize Theorem 2 - the critical radius formula for GG₅ and the emergence
of 1D interval exchange transformations from 2D piecewise isometry systems.

## Module Organization

### 1D Piecewise Isometry Framework (Foundation)

- `TDCSG.Basic`: Core `PiecewiseIsometry` structure, discontinuity sets, partitions
- `TDCSG.Properties`: Partition properties, isometry lemmas, continuity
- `TDCSG.Composition`: Composition and iteration of piecewise isometries
- `TDCSG.MeasurePreserving`: Measure-preserving transformations
- `TDCSG.Finite`: Finite partition specializations
- `TDCSG.IntervalExchange`: **IET infrastructure** - critical for Theorem 2!
- `TDCSG.Examples`: Proven examples (identity, reflection, counterexamples)

### 2D Planar Geometry (New Infrastructure)

- `TDCSG.Planar.Rotations`: Rotations about arbitrary points in ℝ²
  - `rotateAround`: Built using Mathlib's `Orientation.rotation` and `AffineIsometryEquiv`
- `TDCSG.Planar.Disks`: Disk geometry, overlaps, measurability
  - Uses Mathlib's `Metric.closedBall`

### Two-Disk Compound Symmetry Groups

- `TDCSG.CompoundSymmetry.TwoDisk`: Core `TwoDiskSystem` structure
  - Generators a, b (rotations on overlapping disks)
  - Conversion to `PiecewiseIsometry`
  - Notation: `GG_n(r)` and `GG_{n₁,n₂}(r₁,r₂)`
- `TDCSG.CompoundSymmetry.Finiteness`: Critical radius theory
  - `IsFiniteGroup`, `HasInfiniteOrbit`, `CriticalRadius`
  - Theorem 1 statement (if direction)

### Theorem 2: GG₅ Critical Radius (Main Goal)

- `TDCSG.CompoundSymmetry.GG5.Geometry`: Geometric setup
  - Points E, E', F, G (using 5th roots of unity)
  - `r_crit = √(3 + φ)` where φ is the golden ratio
  - `GG5_critical : TwoDiskSystem`

- `TDCSG.CompoundSymmetry.GG5.SegmentMaps`: Three group elements
  - map1, map2, map3: piecewise permutations of segment E'E
  - Bijection theorems for the three interval transformations

- `TDCSG.CompoundSymmetry.GG5.IET`: **1D IET emergence from 2D system**
  - `GG5_induced_IET : IntervalExchangeTransformation 3`
  - Interval lengths involve golden ratio (irrational ratios)
  - Connection to infinite orbit

- `TDCSG.CompoundSymmetry.GG5.CriticalRadius`: **Main Theorem 2**
  - `theorem GG5_critical_radius : CriticalRadius 5 5 = √(3 + φ)`
  - Proof strategy: IET emergence → infinite orbit → critical transition

## Quick Start

### Work with piecewise isometries

```lean
import TDCSG

-- Define a simple piecewise isometry
def myPI : PiecewiseIsometry ℝ := PiecewiseIsometry.id

-- Work with interval exchange transformations
def myIET : IntervalExchangeTransformation 3 := ...
```

### Work with two-disk systems

```lean
import TDCSG

-- Define a two-disk system
def myGG : TwoDiskSystem := GG_5(2.15)  -- GG₅ near critical radius

-- Access generators
#check myGG.genA  -- Left disk rotation
#check myGG.genB  -- Right disk rotation

-- The critical GG₅ system
#check GG5_critical  -- At r = √(3 + φ)

-- Main Theorem 2
#check GG5_critical_radius  -- CriticalRadius 5 5 = √(3 + φ)
```

## Project Status

**Phase:** Scaffolding complete - all files compile with type-correct definitions
**Next:** Fill in proofs starting from geometric lemmas toward Theorem 2
**Build tool:** Use `./check_lean.sh --errors-only` for fast iteration (99% token reduction)

## References

- Paper: *Two-Disk Compound Symmetry Groups* [arXiv:2302.12950v1]
- See README.md for detailed development plan and rigor standards

-/
