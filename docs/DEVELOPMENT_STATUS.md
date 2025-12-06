# TDCSG Development Status

**Last Updated:** December 6, 2025

## Overview

This document tracks the ongoing development of formal proofs for infinite orbits at critical radii across multiple GG(n,n) cases.

## Project Goals

### Short-Term Goal
Formalize the proof of infinite orbits at the critical radius for **GG(10,10)**.

### Long-Term Goals
Extend the formalization to include:
- **GG(8,8)** at its critical radius
- **GG(12,12)** at its critical radius

## Current Status by Case

### GG(5,5) - COMPLETE ✅

| Metric | Value |
|--------|-------|
| Status | **Fully formalized** |
| Sorries | 0 |
| Critical Radius | r_crit = √(3 + φ) ≈ 2.149 |
| IET Structure | 3-interval with cyclic permutation |
| Key Files | `MainTheorem.lean`, `ProofOfMainTheorem.lean` |

The GG(5,5) case is complete with all proofs verified and no sorries.

---

### GG(10,10) - IN PROGRESS 🚧

| Metric | Value |
|--------|-------|
| Status | **Structure complete, algebraic proofs pending** |
| Sorries | 2 (in `AlgebraicIdentities.lean`) |
| Critical Radius | r_crit_10 = √(4 - φ) ≈ 1.543 |
| IET Structure | 2-interval with swap permutation |
| Rotation Number | 1/φ (irrational → infinite orbits) |

#### File Structure

```
TDCSG/GG10/
├── Core.lean                 # ζ₁₀, r_crit_10, power reduction lemmas [COMPLETE]
├── Points.lean               # E₁₀, E'₁₀, segmentPoint₁₀ [COMPLETE]
├── IET.lean                  # 2-interval IET definition [COMPLETE]
├── AlgebraicIdentities.lean  # Word displacement proofs [2 SORRIES]
├── OrbitInfinite.lean        # Infinite orbit theorem [COMPLETE]
└── MainTheorem.lean          # GG10 theorem statement [COMPLETE]
```

#### Remaining Work

1. **Fix cyclotomic lemmas in Core.lean** (lines 298-316)
   - `cyclotomic10_relation` proof needs fixing
   - `zeta10_pow_four_eq` depends on the above
   - Issue: Ring tactic can't close goal with cyclotomic relations

2. **Complete word2_10_algebraic_identity** (AlgebraicIdentities.lean:115-152)
   - Rotation angle conventions have been corrected (ζ₁₀ for Ainv/Binv, ζ₁₀^9 for A/B)
   - Displacement scaled correctly (2 * displacement2_10 for c-space)
   - Need cyclotomic lemmas to prove the final equality

3. **Complete word1_10_algebraic_identity** (AlgebraicIdentities.lean:185+)
   - Similar structure to word2
   - Also has a sorry pending

#### Key Technical Insights Discovered

1. **Generator Convention Mismatch (FIXED)**
   - Generator.A = clockwise rotation = ζ₁₀^9 (not ζ₁₀)
   - Generator.Ainv = counterclockwise rotation = ζ₁₀ (not ζ₁₀^9)
   - Comments in AlgebraicIdentities.lean had these backwards; now corrected

2. **Displacement Scaling Issue (FIXED)**
   - IET.lean defines displacement2_10 = -1/φ (t-space units)
   - Algebraic identity uses c-space (segment parameterized as c*E₁₀ for c ∈ [-1,1])
   - c-space displacement = 2 * t-space displacement
   - Lemma now uses `(2 * displacement2_10) • E₁₀`

3. **Cyclotomic Relations Required**
   - ζ₁₀^5 = -1 (proven)
   - ζ₁₀^8 = -ζ₁₀^3 (proven via ζ₁₀^5)
   - ζ₁₀^9 = -ζ₁₀^4 (proven via ζ₁₀^5)
   - ζ₁₀^4 = ζ₁₀^3 - ζ₁₀^2 + ζ₁₀ - 1 (from 10th cyclotomic polynomial, proof pending)

4. **IET Script Validation**
   - `scripts/find_iet.py --n 10` confirms word2 = a⁻¹b⁻¹ab maps [0.618, 1] → [0, 0.382]
   - Displacement is exactly -1/φ in t-space ✓

---

### GG(8,8) - NOT STARTED 📋

| Metric | Value |
|--------|-------|
| Status | **Not started** |
| Critical Radius | TBD (involves √2) |
| IET Structure | TBD |

#### Preliminary Notes

- Uses 8th roots of unity: ζ₈ = e^(2πi/8) = e^(πi/4)
- Key values: ζ₈ = (1+i)/√2, ζ₈^2 = i, ζ₈^4 = -1
- Critical radius likely involves √2 relationships
- May have 2-interval or 4-interval IET structure

---

### GG(12,12) - NOT STARTED 📋

| Metric | Value |
|--------|-------|
| Status | **Not started** |
| Critical Radius | TBD (involves √3) |
| IET Structure | TBD |

#### Preliminary Notes

- Uses 12th roots of unity: ζ₁₂ = e^(2πi/12) = e^(πi/6)
- Key values: ζ₁₂ = (√3+i)/2, ζ₁₂^2 = ζ₆, ζ₁₂^3 = i, ζ₁₂^6 = -1
- Critical radius likely involves √3 relationships
- Background script `find_iet.py --n 12 --depth 5` was running

---

## Python Scripts for IET Discovery

Located in `scripts/`:

| Script | Purpose |
|--------|---------|
| `find_iet.py` | Search for IET words at given n |
| `find_cyclic_iet.py` | Search for cyclic IET structures |
| `explore_point.py` | Trace orbit of specific point |
| `point_iet_search.py` | Sample-based IET search |

### Usage Examples

```bash
# Activate virtual environment
source .venv/bin/activate

# Find IET for GG(10,10) with default segment
python scripts/find_iet.py --n 10 --depth 5

# Custom segment specification
python scripts/find_iet.py --n 10 --segment="-0.5,0.363271264,0.5,-0.363271264" --depth 5

# Search for cyclic IETs (longer search)
python scripts/find_cyclic_iet.py --n 10 --depth 6

# Explore specific point orbit
python scripts/explore_point.py --n 10 --t 0.5 --depth 8
```

---

## Next Steps to Resume Work

### Immediate Tasks (GG10)

1. **Fix cyclotomic10_relation proof in Core.lean**
   - The lemma states: ζ₁₀^4 - ζ₁₀^3 + ζ₁₀^2 - ζ₁₀ + 1 = 0
   - Need to prove from cyclotomic10_sum using substitutions
   - Current approach using ring_nf fails; try linear_combination or manual calc

2. **Prove zeta10_pow_four_eq**
   - Once cyclotomic10_relation is proven, this follows by algebra
   - May need to avoid linarith (doesn't work on ℂ)

3. **Complete word2_10_algebraic_identity**
   - After cyclotomic lemmas work, use:
     - `zeta10_pow_eight_eq_neg` to substitute ζ₁₀^8 = -ζ₁₀^3
     - `zeta10_pow_nine_eq_neg` to substitute ζ₁₀^9 = -ζ₁₀^4
     - `zeta10_pow_four_eq` to reduce ζ₁₀^4 to lower powers
   - Final equality should then be provable by ring

4. **Complete word1_10_algebraic_identity**
   - Similar approach using compound rotation formulas
   - Uses ζ₁₀^6, ζ₁₀^7, ζ₁₀^8 reduction lemmas

### Medium-Term Tasks

1. **Verify GG10 builds completely** with `lake build`
2. **Run KMVerify** to ensure structure compliance
3. **Document GG10 files** with Mathlib-ready docstrings
4. **Begin GG8 exploration** with Python scripts

---

## Architecture Notes

### Why GG10 is Simpler Than GG5

1. **2-interval IET vs 3-interval**: Fewer cases to track
2. **Swap permutation**: Simpler than cyclic permutation
3. **Direct rotation conjugacy**: 2-interval IET is conjugate to rotation by 1/φ
4. **Irrationality**: 1/φ is irrational → immediate minimality

### Why GG8/GG12 May Differ

1. **Different algebraic numbers**: √2 for GG8, √3 for GG12 (vs φ for GG5/GG10)
2. **Different cyclotomic polynomials**:
   - Φ₈(x) = x⁴ + 1
   - Φ₁₂(x) = x⁴ - x² + 1
3. **Potentially different IET structures**: May have more intervals or different permutations

---

## File Locations Quick Reference

| Purpose | Location |
|---------|----------|
| GG5 Main Theorem | `TDCSG/MainTheorem.lean` |
| GG5 Proof | `TDCSG/ProofOfMainTheorem.lean` |
| GG10 Files | `TDCSG/GG10/*.lean` |
| Python IET Scripts | `scripts/find_iet.py`, etc. |
| Build/Verify | `lake build`, `./check_lean.sh` |
| This Document | `docs/DEVELOPMENT_STATUS.md` |

---

## Contact

For questions about continuing this work, refer to:
- `CLAUDE.md` for coding standards and practices
- The arXiv paper [2302.12950v1](https://arxiv.org/abs/2302.12950) for mathematical background
- `IET_SEGMENTS.md` for segment geometry notes
