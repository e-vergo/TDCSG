# TDCSG - Two-Disk Compound Symmetry Groups

Formal verification in Lean 4 of the critical radius theorem for two-disk compound symmetry groups from [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950).

**Main Theorem (Theorem 2):** GG₅ is infinite at the critical radius r_c = √(3 + φ), where φ = (1 + √5)/2 is the golden ratio.

## Project Status

**Build:** ✅ All 16 files compile successfully
**Sorries:** 24 remaining (1 in Geometry.lean, 23 in SegmentMaps.lean)
**Completion:** ~85% of infrastructure proven, ~15% computational work remaining

## What We Have Proven

### Complete Infrastructure (14 files, 0 sorries)

All foundational theory is complete:
- **Piecewise Isometry Framework**: Definitions, properties, composition, finite partitions
- **Measure Theory**: Measure-preserving transformations, ergodicity concepts
- **Interval Exchange**: Complete IET framework with 3-interval specialization
- **Planar Geometry**: Disk geometry, rotations about points, isometries in ℝ²
- **Two-Disk Systems**: Generator definitions, compound symmetry groups
- **Critical Radius Theory**: r_crit = √(3 + φ) with minimal polynomial x⁴ - 7x² + 11 = 0

### Geometry Module (TDCSG/CompoundSymmetry/GG5/Geometry.lean)

**Key Points and Their Properties:**
- E = ζ₅ - ζ₅² where ζ₅ = e^(2πi/5) (fifth root of unity)
- F = 1 - ζ₅ + ζ₅² - ζ₅³
- G = 2F - E
- E' = -E, F' = -F, G' = -G

**Proven Theorems:**
- ✅ `E_on_left_disk_boundary`: ‖E + 1‖ = r_crit (100+ line proof)
- ✅ `E_in_right_disk`: ‖E - 1‖ < r_crit (strict inequality)
- ✅ `F_eq_psi_times_E`: F = ψ•E where ψ = (√5-1)/2
- ✅ `G_eq_coeff_times_E`: G = (√5-2)•E
- ✅ `one_eq_phi_times_E_plus_zeta5_cube`: 1 = φ•(ζ₅ - ζ₅²) + ζ₅³
- ✅ `translations_irrational`: No integer linear combination of translation lengths equals zero
- ✅ `segment_ratio_is_golden`: ‖E‖/‖F‖ = φ
- ✅ All cyclotomic identities (ζ₅⁵ = 1, ζ₅ + ζ₅⁴ = ψ, etc.)

**Remaining:**
- ⚠️ `GG5_infinite_at_critical_radius`: Final assembly of main theorem (1 sorry)

### Segment Maps Module (TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean)

**Three Critical Group Elements (Corrected to match paper):**
- map1 = a⁻²b⁻¹a⁻¹b⁻¹ maps segment [E',F'] → [G,F]
- map2 = abab² maps segment [F',G'] → [F,E]
- map3 = abab⁻¹a⁻¹b⁻¹ maps segment [G',E] → [E',G]

**Infrastructure in Place:**
- ✅ Generator definitions: genA, genB (rotations by 2π/5)
- ✅ Map definitions correctly implementing the paper's formulas
- ✅ Proof structure for all three bijection theorems
- ✅ Disk preservation proof structure (genA and genB)

**Remaining Work (23 sorries):**

1. **Disk Preservation Helper Lemmas (8 sorries)**
   - `norm_sq_genA_result`, `genA_real_part_expansion`, `lens_implies_right_half`, `genA_norm_sq_bound`
   - Similar set for genB and inverse operations
   - These establish the algebraic inequalities needed for disk preservation

2. **Endpoint Mappings (7 sorries)**
   - map1: E' → G, F' → F
   - map2: F' → F, G' → E
   - map3: G' → E', E → G (one already proven in scratch work)
   - Each requires tracking points through 5-6 generator applications

3. **Bijection Theorems (3 sorries)**
   - `map1_bijection_E'F'_to_GF`
   - `map2_bijection_F'G'_to_FE`
   - `map3_bijection_G'E_to_E'G`
   - Structure complete, waiting on endpoint proofs

4. **Other (5 sorries)**
   - Translation length irrationality (duplicate of Geometry version)
   - Segment membership proofs
   - Final orbit infiniteness theorem

## What Needs to Be Done Next

### Priority 1: Complete Disk Preservation (8 sorries)
**Task:** Finish the algebraic proofs showing genA and genB preserve disk membership for lens points.

**Approach:**
1. Complete the norm squared expansions (partially done)
2. Apply the constraint that lens points have z.re ≤ 0 (left) or z.re ≥ 0 (right)
3. Use cos(2π/5) = (φ-1)/2 identity
4. Apply nlinarith with golden ratio constraints

**Note:** The proof structure is complete; these are algebraic verifications.

### Priority 2: Endpoint Computations (7 sorries)
**Task:** Track each endpoint through its sequence of generators.

**Method:**
1. Start with symbolic representation (e.g., E' = ζ₅² - ζ₅)
2. Apply each generator step-by-step
3. Use cyclotomic identities (ζ₅⁵ = 1, ζ₅⁻¹ = ζ₅⁴, etc.)
4. Simplify with ring tactic

**Example:** map3(E) = G is already computed in scratch work, ready to integrate.

### Priority 3: Complete Bijection Proofs (3 sorries)
**Task:** Prove each map is a bijection between its domain and codomain segments.

**Dependencies:** Requires endpoint mappings from Priority 2.

**Structure:** Already in place - uses isometry preservation and endpoint mappings.

### Priority 4: Final Assembly (1 sorry in Geometry.lean)
**Task:** Combine all pieces to prove GG₅ is infinite at r_crit.

**Dependencies:** All segment maps must be proven.

**Proof outline:** Show the three maps create an IET with irrational translation lengths, implying infinite orbit.

## Build Commands

```bash
# Build entire project
lake build

# Check build status
./check_lean.sh --all sorries TDCSG/

# Build specific module
lake build TDCSG.CompoundSymmetry.GG5.SegmentMaps
```

## Key Files

- `TDCSG/CompoundSymmetry/GG5/Geometry.lean` - Geometric construction (1 sorry)
- `TDCSG/CompoundSymmetry/GG5/SegmentMaps.lean` - Segment transformations (23 sorries)
- `TDCSG/CompoundSymmetry/GG5/IET.lean` - Interval exchange structure (complete)
- `TDCSG/CompoundSymmetry/GG5/CriticalRadius.lean` - Critical radius properties (complete)

## Mathematical Notes

The proof establishes that at r_crit = √(3 + φ):
1. Three specific group elements map segments of the lens intersection
2. These create a 3-interval exchange transformation
3. The translation lengths are irrational multiples of each other
4. Therefore, orbits are infinite, proving GG₅ is infinite

The golden ratio emerges naturally from the fifth roots of unity through the identity ζ₅ + ζ₅⁴ = (√5-1)/2.

## References

- **Paper**: [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950) - Two-Disk Compound Symmetry Groups
- **Authors**: Robert A. Hearn, William Kretschmer, Tomas Rokicki, Benjamin Streeter, Eric Vergo
- **Key Result**: Theorem 2 (page 4) - GG₅ infiniteness at critical radius

## License

Apache 2.0 - See LICENSE file