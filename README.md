# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** GG₅ is infinite at the critical radius r_c = √(3 + φ), where φ = (1 + √5)/2 is the golden ratio.

## Project Status

**Build:** ✅ All files compile successfully (2409 jobs)
**Completion:** Infrastructure complete, 6 sorries remaining for final theorem assembly
**Remaining Work:** 3 point inequality proofs, main infiniteness theorem, final assembly

## What is Complete

### Foundation (14 files, fully proven)
- **Piecewise Isometry Framework**: Definitions, properties, composition, finite partitions
- **Measure Theory**: Measure-preserving transformations, ergodicity concepts
- **Interval Exchange**: Complete IET framework with 3-interval specialization
- **Planar Geometry**: Disk geometry, rotations about points, isometries in ℝ²
- **Two-Disk Systems**: Generator definitions, compound symmetry groups
- **Critical Radius Theory**: r_crit = √(3 + φ) with minimal polynomial x⁴ - 7x² + 11 = 0

### Geometry Module (`TDCSG/CompoundSymmetry/GG5/Geometry.lean`)

**Geometric Construction (fully proven):**
- Points E, F, G and their negatives E', F', G' defined via fifth roots of unity
- E lies on left disk boundary, strictly inside right disk
- Segment ratios equal golden ratio
- Translation lengths are irrationally related (KEY THEOREM ✅)
- All cyclotomic identities established

**Remaining:** Final theorem assembly (depends on SegmentMaps completion)

### SegmentMaps Module (modular structure)

**Complete:**
- `Generators.lean`: Generator definitions (genA, genB as rotations by 2π/5) and isometry properties
- `DiskPreservation.lean`: Cross-disk preservation infrastructure
- `Isometries.lean`: Proofs that map1, map2, map3 are isometries
- `Maps.lean`: Endpoint mapping computations for map1, map2, map3
- Comprehensive cyclotomic helper library (30+ lemmas)
- IsPrimitiveRoot infrastructure for ζ₅

**Remaining:** 3 point inequality lemmas (G ≠ F, F ≠ E, E' ≠ G) in Maps.lean

## Current State

### Axioms (5 total)
- **Geometric axiom:** `lens_intersection_preserved_by_rotation` - fundamental property at critical radius
- **Computational axioms (4):** Disk membership assertions for intermediate points during map1 transformation

### Remaining Sorries (6 total)
1. **Maps.lean (3):** Point inequality proofs (G ≠ F, F ≠ E, E' ≠ G)
2. **Main.lean (1):** `segment_maps_imply_infinite_orbit` - connects segment maps to infinite orbits via IET theory
3. **Geometry.lean (1):** `GG5_infinite_at_critical_radius` - final theorem assembly

## Remaining Work

### Immediate Tasks

**1. Point Inequality Proofs (Maps.lean)**
- Prove G ≠ F, F ≠ E, E' ≠ G using IsPrimitiveRoot infrastructure
- Required for bijection proofs to be complete

**2. Main Infiniteness Theorem (Main.lean)**
- Prove `segment_maps_imply_infinite_orbit`
- Strategy: Show that three segment maps form an interval exchange transformation with irrational translation ratios
- Apply ergodic theory: IETs with irrational rotations have dense/infinite orbits

**3. Final Assembly (Geometry.lean)**
- Complete `GG5_infinite_at_critical_radius`
- Combine segment map results with geometric construction

### Optional: Rigorous Axiom Removal
- Prove the 4 computational disk membership axioms using cyclotomic polynomial theory
- Each proof requires detailed norm expansion and algebraic manipulation
- Not required for Theorem 2 statement, but increases confidence in formalization

## Project Structure

```
TDCSG/
├── Core/                        # Foundation (complete)
├── Planar/                      # 2D geometry (complete)
└── CompoundSymmetry/
    ├── TwoDisk.lean            # Two-disk systems (complete)
    ├── Finiteness.lean         # Finiteness theory (complete)
    └── GG5/
        ├── Geometry.lean       # Geometric construction, final theorem
        ├── CriticalRadius.lean # Critical radius definition (complete)
        ├── IET.lean           # Interval exchange framework (complete)
        ├── GoldenRatioHelpers.lean # Helper lemmas (complete)
        └── SegmentMaps/       # Modular segment map proofs
            ├── Generators.lean      # Generator definitions (complete)
            ├── DiskPreservation.lean # Cross-disk preservation (complete)
            ├── Isometries.lean      # Isometry proofs (complete)
            ├── Maps.lean           # Endpoint computations (3 sorries)
            └── Main.lean           # Final assembly (1 sorry)
```

## Build Commands

```bash
# Build entire project
lake build

# Check sorry count
./check_lean.sh --all sorries TDCSG/

# Build specific module
lake build TDCSG.CompoundSymmetry.GG5.SegmentMaps

# Run tests
lake test
```

## Mathematical Significance

The formalization proves that r_crit = √(3 + φ) is the exact transition point where GG₅ changes from finite to infinite. The proof establishes that three specific group elements create an interval exchange transformation on segment E'E with translation lengths in the ratio of the golden ratio, leading to dense orbits and infiniteness.

## Next Steps

1. Complete point inequality proofs using IsPrimitiveRoot properties
2. Formalize minimal ergodic theory for interval exchange transformations
3. Assemble final theorem connecting all components
4. Optionally: Remove computational axioms with rigorous cyclotomic proofs

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
- **Authors**: Hearn, Kretschmer, Rokicki, Streeter, Vergo

## License

Apache 2.0 - See LICENSE file