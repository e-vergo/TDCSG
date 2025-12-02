# Dead Code Analysis Report

**Generated**: 586051220
**Total declarations**: 423
**Reachable from main theorem**: 309 (73%)
**Unreachable (dead code)**: 57 (13%)

> **Note**: Auto-generated modules (e.g., `TDCSG.CompoundSymmetry.GG5`) are excluded from this report.

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

### TDCSG/Definitions/GroupTheory.lean (10 declarations)

- `TDCSG.Definitions.genA_eq_genA_n_5` (theorem) - Line 41 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genB_eq_genB_n_5` (theorem) - Line 45 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genA_bijective` (theorem) - Line 49 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genB_bijective` (theorem) - Line 54 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genA_perm` (def) - Line 59
- `TDCSG.Definitions.genB_perm` (def) - Line 62
- `TDCSG.Definitions.genA_perm_apply` (theorem) - Line 66 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genB_perm_apply` (theorem) - Line 69 ⚠️ Check for @[simp]
- `TDCSG.Definitions.GG5_orbit` (def) - Line 74
- `TDCSG.Definitions.TwoDiskCompoundSymmetryGroup_5_eq` (theorem) - Line 87 ⚠️ Check for @[simp]

### TDCSG/Definitions/Points.lean (6 declarations)

- `TDCSG.Definitions.F` (def) - Line 42
- `TDCSG.Definitions.G` (def) - Line 45
- `TDCSG.Definitions.t_F` (def) - Line 51
- `TDCSG.Definitions.translation_length_1` (def) - Line 60
- `TDCSG.Definitions.translation_length_2` (def) - Line 63
- `TDCSG.Definitions.segment_length` (def) - Line 66

### TDCSG/Definitions/Core.lean (5 declarations)

- `TDCSG.Definitions.zeta5Circle` (def) - Line 72
- `TDCSG.Definitions.zeta5Circle_coe` (theorem) - Line 76 ⚠️ Check for @[simp]
- `TDCSG.Definitions.zeta5CirclePow` (def) - Line 78
- `TDCSG.Definitions.zeta5CircleInv` (def) - Line 80
- `TDCSG.Definitions.zeta5CircleInv_coe` (theorem) - Line 83 ⚠️ Check for @[simp]

### TDCSG/Definitions/GroupAction.lean (4 declarations)

- `TDCSG.Definitions.genA_in_disk_eq_rotateAboutCircle` (theorem) - Line 52 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genB_in_disk_eq_rotateAboutCircle` (theorem) - Line 56 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genA_preserves_leftDisk` (theorem) - Line 60 ⚠️ Check for @[simp]
- `TDCSG.Definitions.genB_preserves_rightDisk` (theorem) - Line 68 ⚠️ Check for @[simp]

### TDCSG/Proofs/Points.lean (1 declarations)

- `TDCSG.Definitions.psi` (def) - Line 313

## Summary by Module

- `TDCSG.Definitions.Generator`: 17 declarations
- `TDCSG.Definitions.applyGen`: 4 declarations
- `TDCSG.Definitions.wordForIterate`: 2 declarations
- `TDCSG.Definitions.rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.zeta5CirclePow`: 1 declarations
- `TDCSG.Definitions.genB_eq_genB_n_5`: 1 declarations
- `TDCSG.Definitions.genA_bijective`: 1 declarations
- `TDCSG.Definitions.genA_eq_genA_n_5`: 1 declarations
- `TDCSG.Definitions.t_G`: 1 declarations
- `TDCSG.Definitions.zeta5Circle`: 1 declarations
- `TDCSG.Definitions.segment_length`: 1 declarations
- `TDCSG.Definitions.zeta5Circle_coe`: 1 declarations
- `TDCSG.Definitions.E`: 1 declarations
- `TDCSG.Definitions.translation_length_1`: 1 declarations
- `TDCSG.Definitions.genB`: 1 declarations
- `TDCSG.Definitions.genB_bijective`: 1 declarations
- `TDCSG.Definitions.genA_in_disk_eq_rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.genB_perm`: 1 declarations
- `TDCSG.Definitions.φ`: 1 declarations
- `TDCSG.Definitions.genB_in_disk_eq_rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.rotateAboutC`: 1 declarations
- `TDCSG.Definitions.psi`: 1 declarations
- `TDCSG.Definitions.t_F`: 1 declarations
- `TDCSG.Definitions.translation_length_2`: 1 declarations
- `TDCSG.Definitions.genB_perm_apply`: 1 declarations
- `TDCSG.Definitions.GG5_orbit`: 1 declarations
- `TDCSG.Definitions.TwoDiskCompoundSymmetryGroup_5_eq`: 1 declarations
- `TDCSG.Definitions.G`: 1 declarations
- `TDCSG.Definitions.zeta5CircleInv_coe`: 1 declarations
- `TDCSG.Definitions.genA_preserves_leftDisk`: 1 declarations
- `TDCSG.Definitions.GG5_induced_IET`: 1 declarations
- `TDCSG.Definitions.zeta5CircleInv`: 1 declarations
- `TDCSG.Definitions.genB_preserves_rightDisk`: 1 declarations
- `TDCSG.Definitions.genA_perm_apply`: 1 declarations
- `TDCSG.Definitions.F`: 1 declarations
- `TDCSG.Definitions.genA_perm`: 1 declarations
- `TDCSG.Definitions.genA`: 1 declarations

## Recommendations

1. **Check for @[simp] attributes**: Run `python3 scripts/check_simp_attrs.py` first
   - Review `docs/dead_code_safety.txt` for declarations that MUST NOT be deleted
2. **Safe to delete**: `def` declarations without special attributes
3. **Risky to delete**: Theorems/lemmas (check for @[simp] first)
4. **After deletion**: Run `lake build && lake env lean --run KMVerify/Main.lean`
