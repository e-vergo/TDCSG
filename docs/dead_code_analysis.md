# Dead Code Analysis Report

**Generated**: 590918754
**Total declarations**: 406
**Reachable from main theorem**: 309 (76%)
**Unreachable (dead code)**: 103 (25%)

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

### TDCSG/Proofs/Zeta5.lean (17 declarations)

- `TDCSG.CompoundSymmetry.GG5.one_plus_phi_ne_zero` (theorem) - Line 51 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.phi_ne_zero` (theorem) - Line 51 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero` (theorem) - Line 58 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero_re` (theorem) - Line 60 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero_im` (theorem) - Line 62 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_abs_pow4` (theorem) - Line 102 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_add_five_mul` (theorem) - Line 169 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_inv_mul` (theorem) - Line 172 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_inv_as_pow4` (theorem) - Line 175 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_mul_inv` (theorem) - Line 177 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_seventeen` (theorem) - Line 253 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_ten_C` (theorem) - Line 289 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_pow_fifteen_C` (theorem) - Line 290 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_eq` (theorem) - Line 305 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_re_eq_phi` (theorem) - Line 325 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_cubed_im_neg` (theorem) - Line 404 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.normSq_zeta5_cubed_sub_pow4` (theorem) - Line 447 ⚠️ Check for @[simp]

### TDCSG/Proofs/Points.lean (16 declarations)

- `TDCSG.CompoundSymmetry.GG5.E_re` (theorem) - Line 34 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.E_im` (theorem) - Line 53 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.sqrt5_gt_one` (theorem) - Line 297 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.sqrt5_lt_three` (theorem) - Line 305 ⚠️ Check for @[simp]
- `TDCSG.Definitions.psi` (def) - Line 313
- `TDCSG.CompoundSymmetry.GG5.psi_eq` (theorem) - Line 313 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.psi_pos` (theorem) - Line 317 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.psi_ne_zero` (theorem) - Line 319 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.psi_lt_one` (theorem) - Line 321 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.psi_le_one` (theorem) - Line 326 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.psi_lt_t_F` (theorem) - Line 328 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.t_F_lt_one` (theorem) - Line 338 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.zeta5_plus_zeta5_fourth` (theorem) - Line 345 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.F_eq_psi_times_E` (theorem) - Line 425 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.F_on_segment_E'E` (theorem) - Line 447 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.G_eq_coeff_times_E` (theorem) - Line 478 ⚠️ Check for @[simp]

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

### TDCSG/Proofs/CrossDiskRestricted.lean (5 declarations)

- `TDCSG.CompoundSymmetry.GG5.B4_re` (theorem) - Line 352 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.B4_im` (theorem) - Line 357 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.A4_re` (theorem) - Line 362 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.A4_im` (theorem) - Line 370 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.normSq_A4` (theorem) - Line 419 ⚠️ Check for @[simp]

### TDCSG/Proofs/GroupTheory.lean (5 declarations)

- `TDCSG.CompoundSymmetry.GG5.genA_n_bijective_proof` (theorem) - Line 36 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.genB_n_bijective_proof` (theorem) - Line 66 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.CompoundSymmetryGroup_infinite_of_infinite_orbit` (theorem) - Line 273 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.GG5_infinite_of_infinite_orbit` (theorem) - Line 277 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.GG5_has_infinite_group_orbit` (theorem) - Line 281 ⚠️ Check for @[simp]

### TDCSG/Proofs/CrossDiskWord3Helpers.lean (4 declarations)

- `TDCSG.CompoundSymmetry.GG5.A_w3_z1_at_c_lower` (theorem) - Line 78 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.A_w3_z1_at_c_one` (theorem) - Line 84 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.w3_z4_at_one_re` (theorem) - Line 455 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.w3_z4_at_one_im` (theorem) - Line 463 ⚠️ Check for @[simp]

### TDCSG/Proofs/SegmentGeometry.lean (3 declarations)

- `TDCSG.CompoundSymmetry.GG5.F_ne_zero` (theorem) - Line 60 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.E_re_pos` (theorem) - Line 121 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.E'_re_neg` (theorem) - Line 126 ⚠️ Check for @[simp]

### TDCSG/Proofs/OrbitInfinite.lean (2 declarations)

- `TDCSG.CompoundSymmetry.GG5.GG5_IET_orbit_finite_subset` (theorem) - Line 39 ⚠️ Check for @[simp]
- `TDCSG.CompoundSymmetry.GG5.GG5_IET_has_orbit_structure` (theorem) - Line 65 ⚠️ Check for @[simp]

### TDCSG/Proofs/CrossDiskWord2DiskBounds.lean (1 declarations)

- `TDCSG.CompoundSymmetry.GG5.c_lower_word2_eq` (theorem) - Line 40 ⚠️ Check for @[simp]

## Summary by Module

- `TDCSG.CompoundSymmetry.GG5`: 52 declarations
- `TDCSG.Definitions.Generator`: 17 declarations
- `TDCSG.Definitions.applyGen`: 4 declarations
- `TDCSG.Definitions.wordForIterate`: 2 declarations
- `TDCSG.Definitions.rotateAboutCircle`: 1 declarations
- `TDCSG.Definitions.zeta5CirclePow`: 1 declarations
- `TDCSG.Definitions.t_G`: 1 declarations
- `TDCSG.Definitions.genB_eq_genB_n_5`: 1 declarations
- `TDCSG.Definitions.genA_bijective`: 1 declarations
- `TDCSG.Definitions.genA_eq_genA_n_5`: 1 declarations
- `TDCSG.Definitions.zeta5Circle`: 1 declarations
- `TDCSG.Definitions.segment_length`: 1 declarations
- `TDCSG.Definitions.zeta5Circle_coe`: 1 declarations
- `TDCSG.Definitions.E`: 1 declarations
- `TDCSG.Definitions.translation_length_1`: 1 declarations
- `TDCSG.Definitions.genB_bijective`: 1 declarations
- `TDCSG.Definitions.genB_perm`: 1 declarations
- `TDCSG.Definitions.φ`: 1 declarations
- `TDCSG.Definitions.translation_length_2`: 1 declarations
- `TDCSG.Definitions.t_F`: 1 declarations
- `TDCSG.Definitions.rotateAboutC`: 1 declarations
- `TDCSG.Definitions.psi`: 1 declarations
- `TDCSG.Definitions.genB_perm_apply`: 1 declarations
- `TDCSG.Definitions.GG5_orbit`: 1 declarations
- `TDCSG.Definitions.TwoDiskCompoundSymmetryGroup_5_eq`: 1 declarations
- `TDCSG.Definitions.G`: 1 declarations
- `TDCSG.Definitions.zeta5CircleInv_coe`: 1 declarations
- `TDCSG.Definitions.GG5_induced_IET`: 1 declarations
- `TDCSG.Definitions.zeta5CircleInv`: 1 declarations
- `TDCSG.Definitions.genA_perm_apply`: 1 declarations
- `TDCSG.Definitions.F`: 1 declarations
- `TDCSG.Definitions.genA_perm`: 1 declarations

## Recommendations

1. **Check for @[simp] attributes**: Run `python3 scripts/check_simp_attrs.py` first
   - Review `docs/dead_code_safety.txt` for declarations that MUST NOT be deleted
2. **Safe to delete**: `def` declarations without special attributes
3. **Risky to delete**: Theorems/lemmas (check for @[simp] first)
4. **After deletion**: Run `lake build && lake env lean --run KMVerify/Main.lean`
