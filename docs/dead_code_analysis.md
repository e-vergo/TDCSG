# Dead Code Analysis Report

**Generated**: 605072680
**Total declarations**: 359
**Reachable from main theorem**: 319 (88%)
**Unreachable (dead code)**: 43 (11%)

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

### TDCSG/Proofs/Zeta5.lean (3 declarations)

- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_seventeen` (theorem) - Line 253 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_ten_C` (theorem) - Line 297 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_fifteen_C` (theorem) - Line 299 ⚠️ Check for @[simp]

### TDCSG/Definitions/Core.lean (1 declarations)

- `TDCSG.Definitions.Generator.inv_inv` (theorem) - Line 73 ⚠️ Check for @[simp]

## Summary by Module

- `TDCSG.Definitions.Generator`: 18 declarations
- `TDCSG.Definitions.genToPerm`: 4 declarations
- `TDCSG.Definitions.applyGen`: 4 declarations
- `TDCSG.Definitions.wordToPerm`: 3 declarations
- `TDCSG.CompoundSymmetry.GG5`: 3 declarations
- `TDCSG.Definitions.wordForIterate`: 2 declarations
- `TDCSG.Definitions.genB_n_perm`: 2 declarations
- `TDCSG.Definitions.genA_n_perm`: 2 declarations
- `TDCSG.Definitions.rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.rotateAboutC`: 1 declarations
- `TDCSG.Definitions.instInvGenerator`: 1 declarations
- `TDCSG.Definitions.GG5_induced_IET`: 1 declarations
- `TDCSG.Definitions.E`: 1 declarations

## Recommendations

1. **Check for @[simp] attributes**: Run `python3 scripts/check_simp_attrs.py` first
   - Review `docs/dead_code_safety.txt` for declarations that MUST NOT be deleted
2. **Safe to delete**: `def` declarations without special attributes
3. **Risky to delete**: Theorems/lemmas (check for @[simp] first)
4. **After deletion**: Run `lake build && lake env lean --run KMVerify/Main.lean`
