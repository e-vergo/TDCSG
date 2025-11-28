-- Core 1D piecewise isometry framework
import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Composition
import TDCSG.MeasurePreserving
import TDCSG.Finite
import TDCSG.IntervalExchange

-- 2D planar geometry infrastructure
import TDCSG.Rotations
import TDCSG.Disks

-- Two-disk compound symmetry groups
import TDCSG.TwoDisk

-- GG5 IET analysis
import TDCSG.IET
import TDCSG.Orbit
import TDCSG.OrbitInfinite

-- GG5 Geometry (split modules)
import TDCSG.Zeta5
import TDCSG.Points
import TDCSG.SegmentGeometry
import TDCSG.PlaneConversion
import TDCSG.WordCorrespondence

-- Main theorem
import TDCSG.Geometry
import TDCSG.MainTheorem
import TDCSG.ProofOfMainTheorem

/-!
# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification of **Theorem 2** from [arXiv:2302.12950v1]:

**GG5 is infinite at the critical radius r_c = sqrt(3 + phi)**, where phi = (1 + sqrt5)/2
is the golden ratio.

## Module Organization

### Core Framework (6 files)
- `TDCSG.Basic`: Core `PiecewiseIsometry` structure
- `TDCSG.Properties`: Partition properties, continuity
- `TDCSG.Composition`: Composition and iteration
- `TDCSG.MeasurePreserving`: Measure-preserving transformations
- `TDCSG.Finite`: Finite partition specializations
- `TDCSG.IntervalExchange`: IET infrastructure

### 2D Planar Geometry (2 files)
- `TDCSG.Rotations`: Rotations about arbitrary points in R^2
- `TDCSG.Disks`: Disk geometry

### Two-Disk Systems (1 file)
- `TDCSG.TwoDisk`: `TwoDiskSystem` structure, generators

### GG5 Geometry (5 files)
- `TDCSG.Zeta5`: ζ₅ algebra, critical radius
- `TDCSG.Points`: E, E', F, G point definitions and properties
- `TDCSG.SegmentGeometry`: Segment lengths, ratios, irrationality
- `TDCSG.PlaneConversion`: Complex↔Plane conversion, disk membership
- `TDCSG.WordCorrespondence`: Group words, IET correspondence

### Main Theorem (5 files)
- `TDCSG.IET`: `GG5_induced_IET` interval exchange
- `TDCSG.Orbit`: Orbit definitions
- `TDCSG.OrbitInfinite`: `GG5_IET_has_infinite_orbit`
- `TDCSG.Geometry`: Main theorem infrastructure
- `TDCSG.MainTheorem` / `TDCSG.ProofOfMainTheorem`: Kim Morrison Standard

## References
- Paper: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/
