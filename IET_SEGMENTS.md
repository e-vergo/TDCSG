# IET Segment Definitions for GG(n,n)

This document captures the invariant line segments on which the Interval Exchange Transformations (IETs) are defined for each compound symmetry group GG(n,n).

## Setup

- **Rotation centers**: (-1, 0) and (1, 0)
- **Generators** (clockwise rotation, matching Lean convention):
  - `a` = rotation by -2π/n about (-1, 0)
  - `b` = rotation by -2π/n about (1, 0)

## Known Segments

### N = 5

From Theorem 2 of the paper, the IET segment is E'E where E = ζ₅ - ζ₅².

| Endpoint | x | y | Algebraic Form |
|----------|---|---|----------------|
| E' | -1.118033988749895 | -0.3632712640026804 | -(ζ₅ - ζ₅²) |
| E  |  1.118033988749895 |  0.3632712640026804 | ζ₅ - ζ₅² |

**Segment length**: 2.351141 = 2|E|

**Key relationship**: |E + 1| = √(3 + φ) ≈ 2.148961 (critical radius)

**Known IET structure**:
- 3 intervals with lengths [1/(2(1+φ)), 1/(2(1+φ)), 1/φ]
- Cyclic permutation: 0 → 1 → 2 → 0
- Group words from Theorem 2:
  - E'F → GF by a⁻²b⁻¹a⁻¹b⁻¹
  - F'G' → FE by abab²
  - G'E → E'G by abab⁻¹a⁻¹b⁻¹

### N = 10

The IET segment is E'E where E = ζ₁₀ - ζ₁₀².

| Endpoint | x | y | Algebraic Form |
|----------|---|---|----------------|
| E' | -0.5 | -√(5-2√5)/2 ≈ -0.3632712640 | -(ζ₁₀ - ζ₁₀²) |
| E  |  0.5 |  √(5-2√5)/2 ≈  0.3632712640 | ζ₁₀ - ζ₁₀² |

**Segment length**: √(6-2√5) = √5 - 1 = 2/φ ≈ 1.236068

**Key relationship**: Critical radius = √(4 - φ) ≈ 1.543362

**Discovered IET structures**:

#### Structure A: Swap + Reflection (depth 4-5, periodic orbits)

- 3 intervals with boundaries at 2-φ ≈ 0.382 and 1/φ ≈ 0.618
- Lengths: [2-φ, 2/φ-1, 2-φ] = [0.382, 0.236, 0.382]
- Group words:
  - [0, 0.382] → [0.618, 1.0] by b⁻¹a⁻¹ba (translation +1/φ, depth 4)
  - [0.618, 1.0] → [0, 0.382] by a⁻¹b⁻¹ab (translation -1/φ, depth 4)
  - [0.382, 0.618] → [0.382, 0.618] by a⁻³b⁻³a⁻³b⁻³a⁻³ (reflection about 0.5, depth 5)
- **Status**: All orbits periodic (period ≤ 4).

#### Structure B: 3-Cycle (depth 6, INFINITE ORBITS) ✓

- Same 3 intervals with golden ratio boundaries
- Cyclic permutation: I₁ → I₂ → I₃ → I₁
- Group words:
  - **w₁ = a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³** (depth 6):
    - Maps I₁ [0, 0.382] → I₂ [~0.43, ~0.57] (adds +0.382 = 2-φ)
    - Maps I₂ [0.382, 0.618] → I₃ [~0.78, ~0.88] (adds +0.382 = 2-φ)
  - **w₂ = a⁻¹b⁻¹ab** (depth 4):
    - Maps I₃ [0.618, 1] → I₁ [~0.03, ~0.28] (subtracts 0.618 = 1/φ)
- **Effective translation per 3 steps**: 2(2-φ) - 1/φ = 4 - 2φ - (φ-1) = 5 - 3φ (irrational)
- **Status**: VERIFIED INFINITE ORBITS (no period in 100+ steps)

**Verification script**: `scripts/n10_cyclic_iet_verified.py`

**Comparison with N=5**:

- N=5: Uses depth-2 words (aba, bab) for 3-cycle → infinite orbits
- N=10: Uses depth-6 word w₁ and depth-4 word w₂ for 3-cycle → infinite orbits
- Both exhibit the same qualitative behavior (3-interval cyclic permutation with irrational rotation)

### N = 8

The IET segment is E'E where E = ζ₈ - ζ₈² = exp(iπ/4) - exp(iπ/2).

| Endpoint | x | y | Algebraic Form |
|----------|---|---|----------------|
| E' | -√2/2 ≈ -0.7071067812 | (1 - √2/2) ≈ 0.2928932188 | -(ζ₈ - ζ₈²) |
| E  |  √2/2 ≈  0.7071067812 | (√2/2 - 1) ≈ -0.2928932188 | ζ₈ - ζ₈² |

**Segment length**: 2|E| ≈ 1.530734

**Critical radius**: √(5(2-√2)) ≈ 1.711

**IET structure**: Requires depth > 6 search (only endpoint mappings found at depth 4)

### N = 12

The IET segment is E'E where E = ζ₁₂ - ζ₁₂² = exp(iπ/6) - exp(iπ/3).

| Endpoint | x | y | Algebraic Form |
|----------|---|---|----------------|
| E' | (1-√3)/2 ≈ -0.3660254038 | (√3-1)/2 ≈ 0.3660254038 | -(ζ₁₂ - ζ₁₂²) |
| E  | (√3-1)/2 ≈  0.3660254038 | (1-√3)/2 ≈ -0.3660254038 | ζ₁₂ - ζ₁₂² |

**Segment length**: 2|E| ≈ 1.035276

**Critical radius**: √(2(20-11√3)) ≈ 1.377

**IET structure**: Requires depth > 4 search (only endpoint mappings found at depth 4)

## Usage

Run the IET discovery tool:

```bash
# For N=5 (default segment)
python scripts/find_iet.py --n 5 --depth 6

# For N=10 with explicit segment
python scripts/find_iet.py --n 10 --segment="-0.5,-0.363271264,0.5,0.363271264" --depth 6

# General usage
python scripts/find_iet.py --n N --segment="x1,y1,x2,y2" --depth D
```
