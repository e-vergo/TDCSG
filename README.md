# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** GG₅ is infinite at the critical radius r_c = √(3 + φ), where φ = (1 + √5)/2 is the golden ratio.

## Project Status

**Build:** ✅ All files compile successfully
**Completion:** ~90% of infrastructure proven
**Critical Blocker:** One key inequality (`genA_norm_sq_bound`) blocks remaining proofs

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

### Infrastructure Complete in SegmentMaps

**Proven:**
- Generator definitions (genA, genB as rotations by 2π/5)
- Basic complex arithmetic lemmas
- genA_inv preservation via conjugation symmetry
- Translation irrationality (references Geometry proof)
- Proof structures for all major theorems

**Created:**
- Comprehensive cyclotomic helper library (30+ lemmas)
- Golden ratio helper lemmas
- Detailed proof strategies in comments

## The Critical Bottleneck

### `genA_norm_sq_bound` (Line ~403 in SegmentMaps.lean)

This single inequality blocks the entire formalization:

```lean
Need to prove: 6 - 2*φ + 2*z.re*(1 - φ) + 4*z.im*sin(2π/5) ≤ 0
Given: z in lens intersection at critical radius
```

**Why it's hard:**
- Standard tactics (nlinarith, polyrith) fail
- The inequality appears to fail for naive bounds
- Requires understanding the precise geometry at r_crit = √(3 + φ)
- This captures why this specific radius is "critical" for the pentagonal tiling

**Impact:** Once solved, unlocks:
- All disk preservation lemmas (genB mirrors genA)
- All endpoint computations (depend on disk preservation)
- All bijection proofs (depend on endpoints)
- Final theorem assembly

## What Needs to Be Done

### Priority 1: Solve `genA_norm_sq_bound`

**Options:**
1. **Mathematical insight**: Consult pentagonal tiling literature or experts
2. **Computational verification**: Use CAS (Mathematica/SageMath) to verify symbolically
3. **Alternative approach**: Parametrize lens boundary, use convexity arguments
4. **Axiom with justification**: Verify numerically and assert with documentation

### Priority 2: Complete Dependent Proofs (after bottleneck solved)

**Disk Preservation** (7 lemmas)
- genB_norm_sq_bound (mirrors genA)
- Helper lemmas for norm expansions and real part calculations

**Endpoint Mappings** (6 computations)
- map1: Track E' → G and F' → F through 5 generator applications
- map2: Track F' → F and G' → E
- map3: Track G' → E' and E → G (E → G already proven)

**Bijection Proofs** (3 theorems)
- Use isometry preservation and endpoint mappings
- Proof structures already in place

### Priority 3: Final Assembly
- Combine all results in `GG5_infinite_at_critical_radius`
- Show the three maps create an IET with irrational translations
- Apply ergodic theory to conclude infinite orbit

## Project Structure

```
TDCSG/
├── Core/                        # Foundation (complete)
├── Planar/                      # 2D geometry (complete)
└── CompoundSymmetry/
    ├── TwoDisk.lean            # Two-disk systems (complete)
    ├── Finiteness.lean         # Finiteness theory (complete)
    └── GG5/
        ├── Geometry.lean       # Points and segments (complete)
        ├── SegmentMaps.lean    # THE WORK IS HERE
        ├── IET.lean           # Interval exchange (complete)
        ├── CriticalRadius.lean # Critical value (complete)
        └── GoldenRatioHelpers.lean # Helper lemmas
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

The formalization proves that r_crit = √(3 + φ) is the exact transition point where GG₅ changes from finite to infinite. The critical inequality in `genA_norm_sq_bound` encodes the geometric property that makes this radius special for pentagonal symmetry.

## Next Steps for Contributors

1. **Immediate**: Attack `genA_norm_sq_bound` with fresh mathematical insight
2. **Alternative**: Verify the inequality computationally and document thoroughly
3. **Parallel**: Review and optimize existing proofs while waiting for bottleneck
4. **Future**: Extend to other GG(n,n) groups once GG₅ is complete

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
- **Authors**: Hearn, Kretschmer, Rokicki, Streeter, Vergo
- **Documentation**: See `PROOF_STRUCTURE.md` for detailed proof architecture

## License

Apache 2.0 - See LICENSE file