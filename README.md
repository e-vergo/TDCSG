# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** GG₅ is infinite at the critical radius r_c = √(3 + φ), where φ = (1 + √5)/2 is the golden ratio.

## Project Status

| Metric | Value |
|--------|-------|
| Build | ✅ Compiles |
| Sorries | 0 |
| Axioms | 0 |

**Complete.** All theorems fully proven with no gaps.

## Project Structure

```
TDCSG/
├── Basic.lean              # PiecewiseIsometry definition
├── Properties.lean         # Partition properties, continuity
├── Composition.lean        # Composition and iteration
├── MeasurePreserving.lean  # Measure-preserving transformations
├── Finite.lean             # Finite partition specializations
├── IntervalExchange.lean   # IET infrastructure
├── Planar/
│   ├── Rotations.lean      # Rotations about arbitrary points
│   └── Disks.lean          # Disk geometry
└── CompoundSymmetry/
    ├── TwoDisk.lean        # TwoDiskSystem structure
    └── GG5/
        ├── Geometry.lean   # Main theorem: GG5_infinite_at_critical_radius
        ├── IET.lean        # GG5_induced_IET definition
        └── OrbitInfinite.lean  # GG5_IET_has_infinite_orbit
```

## Main Theorems

1. **`GG5_infinite_at_critical_radius`** (Geometry.lean)
   - GG₅ is infinite at r_crit = √(3 + φ)

2. **`GG5_IET_has_infinite_orbit`** (OrbitInfinite.lean)
   - The induced IET has infinite orbits

3. **`GG5_IET_rotation_irrational`** (OrbitInfinite.lean)
   - Interval lengths are irrationally related (golden ratio)

4. **`int_add_int_mul_phi_eq_zero`** (OrbitInfinite.lean)
   - Linear independence: a + b·φ = 0 ⟹ a = b = 0

## Build Commands

```bash
# Build entire project
lake build

# Check sorry count
./check_lean.sh --all sorries TDCSG/

# Build main theorem only
lake build TDCSG.CompoundSymmetry.GG5.Geometry
```

## Mathematical Significance

The formalization proves that r_crit = √(3 + φ) is the exact transition point where GG₅ changes from finite to infinite. The proof establishes that the group generators induce an interval exchange transformation with translation lengths in golden ratio. The irrationality of φ, combined with linear independence of {1, φ} over ℤ, prevents periodic orbits.

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
- **Authors**: Hearn, Kretschmer, Rokicki, Streeter, Vergo

## License

Apache 2.0 - See LICENSE file
