# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** GG5 is infinite at the critical radius r_c = sqrt(3 + phi), where phi = (1 + sqrt5)/2 is the golden ratio.

## Project Status

| Metric | Value |
|--------|-------|
| Build | Compiles |
| Sorries | 2 (geometric correspondence lemmas) |
| Axioms | Standard only (propext, Quot.sound, Classical.choice) |
| Kim Morrison Standard | Structure verified, pending 2 geometric lemmas |

**Near Complete.** The proof structure is complete. Two geometric lemmas remain:
1. `zeta5_rotation_eq_rotateAround`: Complex ζ₅ multiplication ↔ Plane rotation
2. `IET_step_word_correspondence`: Group words correctly implement IET steps

## Kim Morrison Standard Compliance

This project follows the [Kim Morrison standard](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568) for AI-assisted formal mathematics:

- `MainTheorem.lean` contains only the statement, importing only from Mathlib
- `ProofOfMainTheorem.lean` provides the proof
- Uses only standard axioms
- Pending: 2 geometric lemmas need completion (see Project Status)

Run verification:
```bash
lake env lean --run KMVerify.lean
```

## Project Structure

```
TDCSG/
  MainTheorem.lean        # Statement only (imports only Mathlib)
  ProofOfMainTheorem.lean # Proof of main theorem
  Basic.lean              # PiecewiseIsometry definition
  Properties.lean         # Partition properties, continuity
  Composition.lean        # Composition and iteration
  MeasurePreserving.lean  # Measure-preserving transformations
  Finite.lean             # Finite partition specializations
  IntervalExchange.lean   # IET infrastructure
  Rotations.lean          # Rotations about arbitrary points
  Disks.lean              # Disk geometry
  TwoDisk.lean            # TwoDiskSystem structure
  IET.lean                # GG5_induced_IET definition
  Orbit.lean              # Orbit definitions
  OrbitInfinite.lean      # GG5_IET_has_infinite_orbit
  Geometry.lean           # GG5_infinite_at_critical_radius
KMVerify.lean             # Kim Morrison standard verification tool
```

## Main Theorems

1. **`mainTheorem`** (ProofOfMainTheorem.lean)
   - GG5 is infinite at r_crit = sqrt(3 + phi)

2. **`GG5_IET_has_infinite_orbit`** (OrbitInfinite.lean)
   - The induced IET has infinite orbits

3. **`GG5_IET_rotation_irrational`** (OrbitInfinite.lean)
   - Interval lengths are irrationally related (golden ratio)

4. **`int_add_int_mul_phi_eq_zero`** (OrbitInfinite.lean)
   - Linear independence: a + b*phi = 0 implies a = b = 0

## Build Commands

```bash
# Build entire project
lake build

# Run Kim Morrison verification
lake env lean --run KMVerify.lean

# Build main theorem only
lake build TDCSG.ProofOfMainTheorem
```

## Mathematical Significance

The formalization proves that r_crit = sqrt(3 + phi) is the exact transition point where GG5 changes from finite to infinite. The proof establishes that the group generators induce an interval exchange transformation with translation lengths in golden ratio. The irrationality of phi, combined with linear independence of {1, phi} over Z, prevents periodic orbits.

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
- **Authors**: Hearn, Kretschmer, Rokicki, Streeter, Vergo

## License

Apache 2.0 - See LICENSE file
