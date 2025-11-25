-- Core 1D piecewise isometry framework
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Composition
import TDCSG.MeasurePreserving
import TDCSG.Finite
import TDCSG.IntervalExchange

-- 2D planar geometry infrastructure
import TDCSG.Planar.Rotations
import TDCSG.Planar.Disks

-- Two-disk compound symmetry groups
import TDCSG.CompoundSymmetry.TwoDisk

-- Theorem 2: GG₅ critical radius formalization
import TDCSG.CompoundSymmetry.GG5.Geometry
import TDCSG.CompoundSymmetry.GG5.IET
import TDCSG.CompoundSymmetry.GG5.OrbitInfinite

/-!
# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification of **Theorem 2** from [arXiv:2302.12950v1]:

**GG₅ is infinite at the critical radius r_c = √(3 + φ)**, where φ = (1 + √5)/2 is the golden ratio.

## Module Organization

### Core Framework (6 files)
- `TDCSG.Basic`: Core `PiecewiseIsometry` structure
- `TDCSG.Properties`: Partition properties, continuity
- `TDCSG.Composition`: Composition and iteration
- `TDCSG.MeasurePreserving`: Measure-preserving transformations
- `TDCSG.Finite`: Finite partition specializations
- `TDCSG.IntervalExchange`: IET infrastructure

### 2D Planar Geometry (2 files)
- `TDCSG.Planar.Rotations`: Rotations about arbitrary points in ℝ²
- `TDCSG.Planar.Disks`: Disk geometry

### Two-Disk Systems (1 file)
- `TDCSG.CompoundSymmetry.TwoDisk`: `TwoDiskSystem` structure, generators

### Main Theorem (3 files)
- `TDCSG.CompoundSymmetry.GG5.Geometry`: Main theorem `GG5_infinite_at_critical_radius`
- `TDCSG.CompoundSymmetry.GG5.IET`: `GG5_induced_IET` interval exchange
- `TDCSG.CompoundSymmetry.GG5.OrbitInfinite`: `GG5_IET_has_infinite_orbit`

## Axioms (2 total, both in OrbitInfinite.lean)
1. **Keane's Theorem (1975)**: IETs with irrational rotation have no periodic orbits
2. **Non-involution branch**: Unreachable for GG5 (uses swap 0 2 involution)

## References
- Paper: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/
