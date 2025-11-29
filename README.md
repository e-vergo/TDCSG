# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** The compound symmetry group GG₅ at the critical radius is infinite.

## Project Status

| Metric | Value |
|--------|-------|
| Build | Compiles |
| Sorries | 11 (cross-disk membership) |
| Axioms | Standard only (propext, Quot.sound, Classical.choice) |
| Kim Morrison Standard | Structure passes, axiom soundness pending |

**In Progress.** The proof structure is complete but cross-disk membership proofs remain:

| File | Sorries | Description |
|------|---------|-------------|
| Proofs/WordCorrespondence.lean | 11 | Cross-disk membership for intermediate rotation steps |

The remaining sorries are all geometric obligations proving that intermediate points in the word applications stay within the lens-shaped disk intersection. These are the same geometric calculation repeated for each word (word1: 3, word2: 3, word3: 5).

## Main Theorem Statement

```lean
/-- Theorem 2: The compound symmetry group GG₅ at the critical radius is infinite. -/
def StatementOfTheorem : Prop :=
  ∃ p, (orbit GG5_critical.r1 p).Infinite
```

Where:

- `GG5_critical` is the GG(5,5) two-disk system at r_crit = √(3 + φ)
- `orbit r p` is the set of points reachable from p under the group action
- φ = (1 + √5)/2 is the golden ratio

## Kim Morrison Standard Compliance

This project follows the [Kim Morrison standard](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568) for AI-assisted formal mathematics:

- `MainTheorem.lean` contains the statement, importing from Definitions
- `ProofOfMainTheorem.lean` provides the proof
- Uses only standard axioms
- Review burden: 81 lines (MainTheorem + ProofOfMainTheorem)

Run verification:

```bash
lake build TDCSG.ProofOfMainTheorem && lake env lean --run KMVerify.lean
```

## Project Structure

```text
TDCSG/
  MainTheorem.lean          # Statement + GG5_critical definition
  ProofOfMainTheorem.lean   # Proof of main theorem
  Definitions/              # All definitions (no proofs)
    Core.lean               # φ, r_crit, Plane, Word
    Geometry.lean           # Disk geometry, rotations
    GroupAction.lean        # genA, genB, orbit
    TwoDisk.lean            # TwoDiskSystem structure
    IET.lean                # Interval exchange transformations
    ...
  Proofs/                   # All supporting lemmas and proofs
    OrbitInfinite.lean      # GG5_IET_has_infinite_orbit
    WordCorrespondence.lean # IET ↔ group word correspondence
    Geometry.lean           # Geometric analysis
    IntervalExchange.lean   # IET lemmas
    ...
KMVerify.lean               # Kim Morrison standard verification
```

## Proof Architecture

The proof proceeds through:

1. **GG5 Definition**: Two-disk system with 5-fold rotations at critical radius
2. **IET Embedding**: Group action induces interval exchange on segment E'E
3. **Golden Ratio Structure**: Interval lengths are in ratio 1 : φ : φ²
4. **Linear Independence**: {1, φ} linearly independent over ℤ
5. **Infinite Orbits**: No periodic orbits possible → orbits are infinite

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
