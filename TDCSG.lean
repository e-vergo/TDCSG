-- Definitions modules (fundamental constants and types)
import TDCSG.Definitions.Core
import TDCSG.Definitions.Points
import TDCSG.Definitions.Geometry
import TDCSG.Definitions.IET
import TDCSG.Definitions.TwoDisk
import TDCSG.Definitions.RealDynamics
import TDCSG.Definitions.WordCorrespondence
import TDCSG.Definitions.GroupAction

-- Proofs modules
import TDCSG.Proofs.Zeta5
import TDCSG.Proofs.Points
import TDCSG.Proofs.SegmentGeometry
import TDCSG.Proofs.IET
import TDCSG.Proofs.Orbit
import TDCSG.Proofs.OrbitInfinite
import TDCSG.Proofs.WordCorrespondence
import TDCSG.Proofs.Geometry

-- Main theorem
import TDCSG.MainTheorem
import TDCSG.ProofOfMainTheorem

/-!
# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification of **Theorem 2** from [arXiv:2302.12950v1]:

**GG5 is infinite at the critical radius r_c = sqrt(3 + phi)**, where phi = (1 + sqrt5)/2
is the golden ratio.

## Module Organization

### Definitions (8 files)
- `Core`: Fundamental constants (r_c, generators, angles, ζ₅)
- `Points`: E, E', F, G point definitions, segment parameterization
- `Geometry`: Geometric primitives (disks, rotations)
- `IET`: Interval exchange transformation structure
- `TwoDisk`: Two-disk system structure
- `RealDynamics`: Orbit set definitions
- `WordCorrespondence`: Group word definitions
- `GroupAction`: Group action on E'E segment

### Proofs (8 files)
- `Zeta5`: ζ₅ algebraic properties
- `Points`: Point calculation proofs
- `SegmentGeometry`: Segment lengths, disk intersection, rotation correspondence
- `IET`: IET interval properties, `GG5_induced_IET` construction
- `Orbit`: Orbit theory lemmas
- `OrbitInfinite`: `GG5_IET_has_infinite_orbit`
- `WordCorrespondence`: IET-word correspondence proofs
- `Geometry`: Critical radius properties

### Main Theorem (2 files)
- `MainTheorem`: Statement in Kim Morrison Standard format
- `ProofOfMainTheorem`: `GG5_infinite_at_critical_radius`

## References
- Paper: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/
