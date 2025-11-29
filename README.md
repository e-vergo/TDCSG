# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** The compound symmetry group GG5 at the critical radius is infinite.

## Project Status

| Metric | Value |
|--------|-------|
| Build | Compiles |
| Sorries | 8 (cross-disk membership) |
| Axioms | Standard only (propext, Quot.sound, Classical.choice) |
| Kim Morrison Standard | Structure passes, axiom soundness pending |

**In Progress.** The proof structure is complete but cross-disk membership proofs remain:

| File | Sorries | Description |
|------|---------|-------------|
| Proofs/WordCorrespondence.lean | 3 | Cross-disk bounds for word2 intermediate steps (z1, z2, z3) |
| Proofs/CrossDiskBounds.lean | 5 | Cross-disk bounds for word3 intermediate steps (z1-z5) |

The remaining sorries are geometric obligations proving that intermediate points in word applications stay within the lens-shaped disk intersection. Word1 bounds are complete; word2 needs 3 bounds and word3 needs 5 bounds.

## Main Theorem Statement

```lean
/-- Theorem 2: The compound symmetry group GG5 at the critical radius is infinite. -/
def StatementOfTheorem : Prop :=
  exists p, (orbit GG5_critical.r1 p).Infinite
```

Where:

- `GG5_critical` is the GG(5,5) two-disk system at r_crit = sqrt(3 + phi)
- `orbit r p` is the set of points reachable from p under the group action
- phi = (1 + sqrt(5))/2 is the golden ratio

## Architecture

The codebase uses a complex-native architecture:

- **Primary type**: Complex numbers (C) as source of truth
- **Rotation system**: Mathlib's `Circle` type with `rotation : Circle ->* C =(li)[R] C`
- **Rotation direction**: Clockwise (-2pi/5) using zeta5^4, matching the paper
- **Generator encoding**: Inductive type `Generator` with A, Ainv, B, Binv constructors

## Kim Morrison Standard Compliance

This project follows the [Kim Morrison standard](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568) for AI-assisted formal mathematics:

- `MainTheorem.lean` contains the statement, importing from Definitions
- `ProofOfMainTheorem.lean` provides the proof (no sorries)
- Uses only standard axioms

Run verification:

```bash
lake build TDCSG.ProofOfMainTheorem && lake env lean --run KMVerify.lean
```

## Project Structure

```text
TDCSG/
  MainTheorem.lean          # Statement + GG5_critical definition
  ProofOfMainTheorem.lean   # Proof of main theorem
  Definitions/              # All definitions (9 files)
    Core.lean               # phi, psi, r_crit, Generator, Word
    Cyclotomic.lean         # zeta5 definition
    Geometry.lean           # Disk geometry, rotations (C-native)
    GroupAction.lean        # genA, genB, applyWord, orbit
    TwoDisk.lean            # TwoDiskSystem structure
    IET.lean                # Interval exchange transformations
    Points.lean             # E, E', F, G, segmentPoint
    Orbit.lean              # Orbit definitions
    WordCorrespondence.lean # word1, word2, word3 definitions
  Proofs/                   # All supporting lemmas (9 files)
    Zeta5.lean              # zeta5 identities, zeta5Circle
    Points.lean             # Point properties, F/G scalar relations
    OrbitInfinite.lean      # GG5_IET_has_infinite_orbit
    WordCorrespondence.lean # IET <-> group word correspondence (3 sorries)
    CrossDiskBounds.lean    # Cross-disk membership bounds (5 sorries)
    Geometry.lean           # r_crit lemmas
    SegmentGeometry.lean    # Segment lengths and ratios
    IET.lean                # IET interval properties
    Orbit.lean              # Orbit theory lemmas
KMVerify.lean               # Kim Morrison standard verification
```

## Proof Architecture

The proof proceeds through:

1. **GG5 Definition**: Two-disk system with 5-fold rotations at critical radius
2. **IET Embedding**: Group action induces interval exchange on segment E'E
3. **Golden Ratio Structure**: Interval lengths are in ratio 1 : phi : phi^2
4. **Linear Independence**: {1, phi} linearly independent over Z
5. **Infinite Orbits**: No periodic orbits possible -> orbits are infinite

## Build Commands

```bash
# Build entire project
lake build

# Build main theorem only
lake build TDCSG.ProofOfMainTheorem

# Run Kim Morrison verification
lake env lean --run KMVerify.lean
```

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
- **Authors**: Hearn, Kretschmer, Rokicki, Streeter, Vergo

## License

Apache 2.0 - See LICENSE file
