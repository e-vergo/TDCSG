# TDCSG Completion Status

**Target:** Zero sorries, zero axioms.

## Current State

| Metric | Value |
|--------|-------|
| Sorries | 1 |
| Location | `OrbitInfinite.lean:500` in `GG5_IET_no_periodic_orbits` |
| Build | ✅ Compiles (with sorry warning) |

## The Remaining Gap

**Theorem:** `GG5_IET_no_periodic_orbits : ∀ x ∈ [0,1), ¬IsPeriodic GG5_induced_IET.toFun x`

**What's proven:**
- `int_add_int_mul_phi_eq_zero`: If `a + b·φ = 0` for integers, then `a = b = 0`
- `GG5_IET_rotation_irrational`: length₂/length₁ = φ is irrational
- `length1_lt_half`, `interval2_image_bound`, `denom_eq_two_one_plus_phi`
- All supporting infrastructure

**What's missing:** Connecting displacement equation to `int_add_int_mul_phi_eq_zero`.

## Proof Strategy (~80 lines)

### The Algebraic Argument

For k-periodic orbit with visit counts n₀, n₁, n₂:

1. **Displacements** (shift when visiting interval i):
   - d₀ = rangeLeft(2) - 0 = length₃ + length₂ = 1/2
   - d₁ = rangeLeft(1) - length₁ = length₃ - length₁ = (φ²-1)/D = φ/D
   - d₂ = 0 - (length₁ + length₂) = -1/2

2. **Periodicity equation:** `n₀(1/2) + n₁(φ/D) - n₂(1/2) = 0`

3. **Simplify:** `(n₀ - n₂)/2 + n₁·φ/(1+φ+φ²) = 0`

4. **Using D = 2(1+φ):** `(n₀ - n₂)(1+φ) + n₁·φ = 0`

5. **Expand:** `(n₀ - n₂) + (n₀ - n₂ + n₁)·φ = 0`

6. **Apply `int_add_int_mul_phi_eq_zero`:**
   - n₀ - n₂ = 0
   - n₀ - n₂ + n₁ = 0
   - ∴ n₁ = 0

7. **Dynamics contradiction:** If n₁ = 0, orbit never visits interval 1.
   But interval 2 maps to [0, 1/2) which contains interval 1 = [length₁, 1/2).
   Any orbit from interval 2 must eventually hit interval 1. Contradiction.

### Implementation Plan

```lean
-- 1. Define displacement function (~10 lines)
noncomputable def displacement (i : Fin 3) : ℝ :=
  GG5_induced_IET.rangeLeft (GG5_induced_IET.permutation i) - GG5_induced_IET.domainLeft i

-- 2. Prove displacement values (~20 lines)
theorem displacement_0 : displacement 0 = 1/2
theorem displacement_1 : displacement 1 = goldenRatio / (1 + goldenRatio + goldenRatio^2)
theorem displacement_2 : displacement 2 = -1/2

-- 3. Define visit count (~15 lines)
def visitCount (x : ℝ) (k : ℕ) (i : Fin 3) : ℕ :=
  (Finset.range k).filter (fun j => (GG5_induced_IET.toFun^[j]) x ∈ GG5_induced_IET.interval i) |>.card

-- 4. Prove visit counts sum to k (~5 lines)
theorem visitCount_sum : visitCount x k 0 + visitCount x k 1 + visitCount x k 2 = k

-- 5. Periodicity implies displacement equation (~15 lines)
theorem periodic_displacement_eq (hper : (f^[k]) x = x) :
    n₀ * d₀ + n₁ * d₁ + n₂ * d₂ = 0

-- 6. Apply int_add_int_mul_phi_eq_zero to get n₁ = 0 (~10 lines)
theorem periodic_forces_n1_zero : visitCount x k 1 = 0

-- 7. Prove interval 2 eventually maps to interval 1 (~15 lines)
theorem interval2_reaches_interval1 (x ∈ interval 2) : ∃ j, (f^[j]) x ∈ interval 1

-- 8. Derive contradiction (~5 lines)
```

## Key Files

| File | Role |
|------|------|
| `OrbitInfinite.lean:331-502` | Contains sorry, add proof here |
| `OrbitInfinite.lean:251-272` | `int_add_int_mul_phi_eq_zero` (proven) |
| `IET.lean:140-163` | `GG5_induced_IET` definition |
| `IntervalExchange.lean` | `rangeLeft`, `domainLeft`, `toFun` |

## Commands

```bash
lake build                                    # Build
./check_lean.sh --all sorries TDCSG/         # Verify 0 sorries
```

## Success Criteria

- [ ] `lake build` succeeds
- [ ] `./check_lean.sh --all sorries TDCSG/` returns 0
- [ ] Update README.md: "0 axioms"
