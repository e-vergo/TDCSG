# Dead Code Analysis by File

**Total: 120 unreachable declarations across 12 files**

## Quick Summary

**Definitions/** (25 declarations, 21%):
- 5 files with dead code
- 12 defs, 13 theorems
- 7 have @[simp] attributes (MUST NOT DELETE)

**Proofs/** (64 declarations, 53%):
- 7 files with dead code
- 1 def, 63 theorems
- 12 have @[simp] attributes (MUST NOT DELETE)

## Files Ranked by Dead Code Count

| Rank | File | Dead | Defs | Theorems | @[simp] |
|------|------|------|------|----------|---------|
| 1 | Proofs/Zeta5.lean | 17 | 0 | 17 | 12 |
| 2 | Proofs/Points.lean | 16 | 1 | 15 | 0 |
| 3 | Proofs/GroupTheory.lean | 16 | 0 | 16 | 0 |
| 4 | Definitions/GroupTheory.lean | 10 | 3 | 7 | 2 |
| 5 | Definitions/Points.lean | 6 | 6 | 0 | 0 |
| 6 | Definitions/Core.lean | 5 | 3 | 2 | 5 |
| 7 | Proofs/CrossDiskRestricted.lean | 5 | 0 | 5 | 0 |
| 8 | Definitions/GroupAction.lean | 4 | 0 | 4 | 0 |
| 9 | Proofs/CrossDiskWord3Helpers.lean | 4 | 0 | 4 | 0 |
| 10 | Proofs/SegmentGeometry.lean | 3 | 0 | 3 | 0 |
| 11 | Proofs/OrbitInfinite.lean | 2 | 0 | 2 | 0 |
| 12 | Proofs/CrossDiskWord2DiskBounds.lean | 1 | 0 | 1 | 0 |

## Safety Analysis

**DANGEROUS - 19 declarations with @[simp]:**
- Definitions/Core.lean: 5 declarations
- Definitions/GroupTheory.lean: 2 declarations
- Proofs/Zeta5.lean: 12 declarations

**POTENTIALLY SAFE - 68 declarations without attributes:**
- Definitions/Points.lean: 6 defs (all safe)
- Definitions/GroupTheory.lean: 8 declarations
- Definitions/GroupAction.lean: 4 theorems
- Proofs/Points.lean: 16 theorems
- Proofs/GroupTheory.lean: 16 theorems
- Proofs/Zeta5.lean: 5 theorems (rest have @[simp])
- Other Proofs/ files: 13 theorems

## Detailed Breakdown

### TDCSG/Definitions/Core.lean (5 declarations)
**ALL 5 have @[simp] - DO NOT DELETE**

- `zeta5Circle` (def) - Line 72 [@simp]
- `zeta5Circle_coe` (theorem) - Line 76 [@simp]
- `zeta5CirclePow` (def) - Line 78 [@simp]
- `zeta5CircleInv` (def) - Line 80 [@simp]
- `zeta5CircleInv_coe` (theorem) - Line 83 [@simp]

### TDCSG/Definitions/GroupAction.lean (4 declarations)
**All safe to delete**

- `genA_in_disk_eq_rotateAboutCircle` (theorem) - Line 52
- `genB_in_disk_eq_rotateAboutCircle` (theorem) - Line 56
- `genA_preserves_leftDisk` (theorem) - Line 60
- `genB_preserves_rightDisk` (theorem) - Line 68

### TDCSG/Definitions/GroupTheory.lean (10 declarations)
**2 have @[simp], 8 potentially safe**

- `genA_eq_genA_n_5` (theorem) - Line 41
- `genB_eq_genB_n_5` (theorem) - Line 45
- `genA_bijective` (theorem) - Line 49
- `genB_bijective` (theorem) - Line 54
- `genA_perm` (def) - Line 59
- `genB_perm` (def) - Line 62
- `genA_perm_apply` (theorem) - Line 66 [@simp]
- `genB_perm_apply` (theorem) - Line 69 [@simp]
- `GG5_orbit` (def) - Line 74
- `TwoDiskCompoundSymmetryGroup_5_eq` (theorem) - Line 87

### TDCSG/Definitions/Points.lean (6 declarations)
**All safe to delete**

- `F` (def) - Line 38
- `G` (def) - Line 41
- `t_F` (def) - Line 47
- `translation_length_1` (def) - Line 56
- `translation_length_2` (def) - Line 59
- `segment_length` (def) - Line 62

### TDCSG/Proofs/Zeta5.lean (17 declarations)
**12 have @[simp], 5 potentially safe**

Safe to delete:
- `phi_ne_zero` (theorem) - Line 51
- `one_plus_phi_ne_zero` (theorem) - Line 51
- `zeta5_inv_as_pow4` (theorem) - Line 175
- `zeta5_pow_mul_inv` (theorem) - Line 177
- `zeta5_eq` (theorem) - Line 305

DANGEROUS [@simp]:
- `zeta5_pow_zero` (theorem) - Line 58
- `zeta5_pow_zero_re` (theorem) - Line 60
- `zeta5_pow_zero_im` (theorem) - Line 62
- `zeta5_abs_pow4` (theorem) - Line 102
- `zeta5_inv_mul` (theorem) - Line 172
- `zeta5_pow_add_five_mul` (theorem) - Line 169
- `zeta5_pow_seventeen` (theorem) - Line 253
- `zeta5_pow_ten_C` (theorem) - Line 289
- `zeta5_pow_fifteen_C` (theorem) - Line 290
- `zeta5_re_eq_phi` (theorem) - Line 325
- `zeta5_cubed_im_neg` (theorem) - Line 404
- `normSq_zeta5_cubed_sub_pow4` (theorem) - Line 447

### TDCSG/Proofs/Points.lean (16 declarations)
**All safe to delete**

- `E_re` (theorem) - Line 34
- `E_im` (theorem) - Line 53
- `sqrt5_gt_one` (theorem) - Line 297
- `sqrt5_lt_three` (theorem) - Line 305
- `psi` (def) - Line 313
- `psi_eq` (theorem) - Line 313
- `psi_pos` (theorem) - Line 317
- `psi_ne_zero` (theorem) - Line 319
- `psi_lt_one` (theorem) - Line 321
- `psi_le_one` (theorem) - Line 326
- `psi_lt_t_F` (theorem) - Line 328
- `t_F_lt_one` (theorem) - Line 338
- `zeta5_plus_zeta5_fourth` (theorem) - Line 345
- `F_eq_psi_times_E` (theorem) - Line 425
- `F_on_segment_E'E` (theorem) - Line 447
- `G_eq_coeff_times_E` (theorem) - Line 478

### TDCSG/Proofs/GroupTheory.lean (16 declarations)
**All safe to delete**

- `Circle_exp_neg_two_pi_over_5_pow_5` (theorem) - Line 36
- `genA_outside` (theorem) - Line 42
- `genA_inside` (theorem) - Line 46
- `genA_pow_five` (theorem) - Line 52
- `genA_bijective_proof` (theorem) - Line 84
- `genB_outside` (theorem) - Line 102
- `genB_inside` (theorem) - Line 106
- `genB_pow_five` (theorem) - Line 112
- `genB_bijective_proof` (theorem) - Line 172
- `genA_perm_pow_five` (theorem) - Line 190
- `genB_perm_pow_five` (theorem) - Line 196
- `genA_n_bijective_proof` (theorem) - Line 202
- `genB_n_bijective_proof` (theorem) - Line 232
- `CompoundSymmetryGroup_infinite_of_infinite_orbit` (theorem) - Line 439
- `GG5_infinite_of_infinite_orbit` (theorem) - Line 443
- `GG5_has_infinite_group_orbit` (theorem) - Line 447

### Other Files (15 declarations total)
**All safe to delete**

Smaller files with 1-5 declarations each:
- CrossDiskRestricted.lean: 5 theorems
- CrossDiskWord3Helpers.lean: 4 theorems
- SegmentGeometry.lean: 3 theorems
- OrbitInfinite.lean: 2 theorems
- CrossDiskWord2DiskBounds.lean: 1 theorem
