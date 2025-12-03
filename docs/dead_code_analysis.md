# Dead Code Analysis Report

**Generated**: 600121138
**Total declarations**: 375
**Reachable from main theorem**: 319 (85%)
**Unreachable (dead code)**: 59 (15%)

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

- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero` (theorem) - Line 50 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero_re` (theorem) - Line 52 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero_im` (theorem) - Line 54 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_abs_pow4` (theorem) - Line 94 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_add_five_mul` (theorem) - Line 161 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_inv_mul` (theorem) - Line 164 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_seventeen` (theorem) - Line 238 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_ten_C` (theorem) - Line 274 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_fifteen_C` (theorem) - Line 275 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_re_eq_phi` (theorem) - Line 304 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_cubed_im_neg` (theorem) - Line 383 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.normSq_zeta5_cubed_sub_pow4` (theorem) - Line 426 ⚠️ Check for @[simp]

### TDCSG/Definitions/Core.lean (6 declarations)

- `TDCSG.Definitions.Generator.inv_inv` (theorem) - Line 74 ⚠️ Check for @[simp]
- `TDCSG.Definitions.zeta5Circle` (def) - Line 127
- `TDCSG.Definitions.zeta5Circle_coe` (theorem) - Line 131 ⚠️ Check for @[simp]
- `TDCSG.Definitions.zeta5CirclePow` (def) - Line 133
- `TDCSG.Definitions.zeta5CircleInv` (def) - Line 135
- `TDCSG.Definitions.zeta5CircleInv_coe` (theorem) - Line 138 ⚠️ Check for @[simp]

## Summary by Module

- `TDCSG.Definitions.Generator`: 18 declarations
- `TDCSG.CompoundSymmetry.GG5`: 12 declarations
- `TDCSG.Definitions.genToPerm`: 4 declarations
- `TDCSG.Definitions.applyGen`: 4 declarations
- `TDCSG.Definitions.wordToPerm`: 3 declarations
- `TDCSG.Definitions.wordForIterate`: 2 declarations
- `TDCSG.Definitions.genB_n_perm`: 2 declarations
- `TDCSG.Definitions.genA_n_perm`: 2 declarations
- `TDCSG.Definitions.rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.zeta5CirclePow`: 1 declarations
- `TDCSG.Definitions.rotateAboutC`: 1 declarations
- `TDCSG.Definitions.psi`: 1 declarations
- `TDCSG.Definitions.instInvGenerator`: 1 declarations
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
