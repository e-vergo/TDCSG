# Dead Code Analysis Report

**Generated**: 593961350
**Total declarations**: 352
**Reachable from main theorem**: 309 (87%)
**Unreachable (dead code)**: 49 (13%)

## ⚠️ IMPORTANT WARNINGS

1. **@[simp] lemmas**: Run `python3 scripts/check_simp_attrs.py` to identify declarations with @[simp] attributes
   - See `docs/dead_code_safety.txt` for the list of @[simp] declarations
   - `@[simp]` lemmas are used implicitly by tactics and MUST NOT be deleted

2. **Supporting lemmas**: Some unreachable lemmas may be:
   - Alternative proof approaches kept for reference
   - Exploratory work that may be useful later
   - General-purpose utilities not yet needed

3. **Before deleting**: Always run `lake build` after deletions to verify

## Unreachable Declarations by File

### TDCSG/Proofs/Zeta5.lean (12 declarations)

- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero` (theorem) - Line 54 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero_re` (theorem) - Line 56 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero_im` (theorem) - Line 58 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_abs_pow4` (theorem) - Line 98 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_add_five_mul` (theorem) - Line 165 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_inv_mul` (theorem) - Line 168 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_seventeen` (theorem) - Line 242 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_ten_C` (theorem) - Line 278 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_fifteen_C` (theorem) - Line 279 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_re_eq_phi` (theorem) - Line 308 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_cubed_im_neg` (theorem) - Line 387 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.normSq_zeta5_cubed_sub_pow4` (theorem) - Line 430 ⚠️ Check for @[simp]

### TDCSG/Definitions/Core.lean (5 declarations)

- `TDCSG.Definitions.zeta5Circle` (def) - Line 72
- `TDCSG.Definitions.zeta5Circle_coe` (theorem) - Line 76 ⚠️ Check for @[simp]
- `TDCSG.Definitions.zeta5CirclePow` (def) - Line 78
- `TDCSG.Definitions.zeta5CircleInv` (def) - Line 80
- `TDCSG.Definitions.zeta5CircleInv_coe` (theorem) - Line 83 ⚠️ Check for @[simp]

### TDCSG/Definitions/GroupTheory.lean (2 declarations)

- `TDCSG.Definitions.genA_eq_genA_n_5` (theorem) - Line 30 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genB_eq_genB_n_5` (theorem) - Line 34 ⚠️ Check for @[simp]

### TDCSG/Proofs/Points.lean (1 declarations)

- `TDCSG.Definitions.psi` (def) - Line 271

## Summary by Module

- `TDCSG.Definitions.Generator`: 17 declarations
- `TDCSG.CompoundSymmetry.GG5`: 12 declarations
- `TDCSG.Definitions.applyGen`: 4 declarations
- `TDCSG.Definitions.wordForIterate`: 2 declarations
- `TDCSG.Definitions.rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.zeta5CirclePow`: 1 declarations
- `TDCSG.Definitions.rotateAboutC`: 1 declarations
- `TDCSG.Definitions.psi`: 1 declarations
- `TDCSG.Definitions.t_G`: 1 declarations
- `TDCSG.Definitions.genB_eq_genB_n_5`: 1 declarations
- `TDCSG.Definitions.genA_eq_genA_n_5`: 1 declarations
- `TDCSG.Definitions.zeta5Circle`: 1 declarations
- `TDCSG.Definitions.zeta5CircleInv_coe`: 1 declarations
- `TDCSG.Definitions.zeta5Circle_coe`: 1 declarations
- `TDCSG.Definitions.GG5_induced_IET`: 1 declarations
- `TDCSG.Definitions.zeta5CircleInv`: 1 declarations
- `TDCSG.Definitions.E`: 1 declarations
- `TDCSG.Definitions.φ`: 1 declarations

## Recommendations

1. **Check for @[simp] attributes**: Run `python3 scripts/check_simp_attrs.py` first
   - Review `docs/dead_code_safety.txt` for declarations that MUST NOT be deleted
2. **Safe to delete**: `def` declarations without special attributes
3. **Risky to delete**: Theorems/lemmas (check for @[simp] first)
4. **After deletion**: Run `lake build && lake env lean --run KMVerify/Main.lean`
