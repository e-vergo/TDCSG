# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** The compound symmetry group GG5 at the critical radius is infinite.

## Project Status

| Metric | Value |
|--------|-------|
| Build | Compiles (2402 jobs) |
| Sorries | 0 |
| Axioms | Standard only (propext, Quot.sound, Classical.choice, funext) |
| Kim Morrison Standard | All 11 checks pass |

**Complete.** All proofs are fully formalized with no sorries.

## KMVerify Results

```
================================================================================
KIM MORRISON STANDARD VERIFICATION
Project: TDCSG
================================================================================

TRUST TIER SUMMARY
--------------------------------------------------------------------------------
  MathlibExtensions/          [NOT PRESENT]
  Definitions/                7 files     847 lines
  Proofs/                     18 files    7834 lines
  MainTheorem.lean                        28 lines
  ProofOfMainTheorem.lean                 60 lines
--------------------------------------------------------------------------------
  REVIEW BURDEN: 875 lines (Definitions + MainTheorem)
  TOTAL: 8769 lines (9% requires review)

CHECKS
--------------------------------------------------------------------------------
  [PASS] Structure
  [PASS] Axioms
  [PASS] Transparency
  [PASS] Completeness
  [PASS] Proof Minimality
  [PASS] No Duplicates
  [PASS] Imports
  [PASS] MainTheorem Purity
  [PASS] No Instances
  [PASS] No Trivial Definitions
  [PASS] Proofs Declarations

================================================================================
RESULT: PROJECT VERIFIED
================================================================================
```

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

- `MainTheorem.lean` contains the statement, importing only from Definitions
- `ProofOfMainTheorem.lean` provides the proof
- `Definitions/` contains all definitions (human-reviewable)
- `Proofs/` contains only lemmas and theorems (no definitions)
- Uses only standard axioms

Run verification:

```bash
lake build && lake env lean --run KMVerify/Main.lean
```

## Project Structure

```text
TDCSG/
  MainTheorem.lean            # Statement + GG5_critical definition
  ProofOfMainTheorem.lean     # Proof of main theorem
  Definitions/                # All definitions (7 files, 847 lines)
    Core.lean                 # phi, r_crit, Generator, Word, zeta5, Circle defs
    Geometry.lean             # Disk geometry, rotations, TwoDiskSystem
    GroupAction.lean          # genA, genB, applyWord, orbit
    IET.lean                  # Interval exchange transformations, IET_word, wordForIterate
    Points.lean               # E, E', F, G, segmentPoint
    RealDynamics.lean         # Orbit definitions, GG5_displacement
    WordCorrespondence.lean   # word1, word2, word3 definitions
  Proofs/                     # All supporting lemmas (18 files, 7834 lines)
    Zeta5.lean                # zeta5 identities
    Points.lean               # Point properties, F/G scalar relations
    OrbitInfinite.lean        # GG5_IET_has_infinite_orbit
    Word1Correspondence.lean  # Word1 produces displacement0
    Word2Correspondence.lean  # Word2 produces displacement1
    Word3Correspondence.lean  # Word3 produces displacement2
    CrossDiskBasic.lean       # Basic cross-disk lemmas
    CrossDiskRestricted.lean  # Restricted cross-disk bounds
    CrossDiskWord2DiskBounds.lean  # Cross-disk bounds for word2
    CrossDiskWord3DiskBounds.lean  # Cross-disk bounds for word3
    CrossDiskWord3Helpers.lean     # Helper lemmas for word3 bounds
    Geometry.lean             # r_crit lemmas
    SegmentGeometry.lean      # Segment lengths and ratios
    IET.lean                  # IET interval properties
    IETOrbit.lean             # IET orbit theorems
    Orbit.lean                # Orbit theory lemmas
    AlgebraicIdentities.lean  # Algebraic identity lemmas
    RotationFormulas.lean     # Rotation formula lemmas
KMVerify/                     # Kim Morrison standard verification tool
  Main.lean                   # CLI entry point
  Config.lean                 # Configuration parsing
  Checks/                     # Individual verification checks
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
lake env lean --run KMVerify/Main.lean

# JSON output for CI
lake env lean --run KMVerify/Main.lean --json
```

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
- **Authors**: Hearn, Kretschmer, Rokicki, Streeter, Vergo

## License

Apache 2.0 - See LICENSE file
