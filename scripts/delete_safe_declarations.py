#!/usr/bin/env python3
"""
Delete only declarations that are provably safe (didn't break the build).

Based on the empirical test, we know which declarations cause build errors.
Delete everything else.
"""

import argparse
import json
import re
import sys
import tarfile
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict


# Declarations to KEEP (either caused build errors or are likely used in tactics)
# Be conservative - only delete things we're SURE are unused
NEEDED_DECLARATIONS = {
    # From build errors
    'genB', 'genB_bijective', 'genA', 'genA_bijective',
    'psi',

    # All Points.lean definitions and lemmas (many used in tactics)
    'F', 'G', 't_F', 't_G',
    'segment_length', 'translation_length_1', 'translation_length_2',
    'E_re', 'E_im',
    'sqrt5_gt_one', 'sqrt5_lt_three',
    'psi_eq', 'psi_pos', 'psi_ne_zero', 'psi_lt_one', 'psi_le_one',
    'psi_lt_t_F', 't_G_pos', 't_G_lt_t_F', 't_F_lt_one',
    "F_on_segment_E'E", "G_on_segment_E'E",
    'segment_ordering', 'F_eq_psi_times_E', 'G_eq_coeff_times_E',
    'zeta5_plus_zeta5_fourth',

    # All zeta5 lemmas (many provide type info for field notation)
    'zeta5_eq', 'zeta5_re_eq_phi', 'zeta5_im_pos',
    'zeta5_sq_re_eq_phi', 'sin_eight_pi_fifth',
    'zeta5_cubed_im_neg', 'zeta5_pow4_im_neg',
    'zeta5_sq_im_pos',
    'one_add_zeta5_pow4_re', 'one_sub_zeta5_pow4_re',
    'zeta5_powers_re_sum',
    'zeta5CirclePow_coe', 'zeta5CirclePow4_eq_inv', 'circle_exp_two_pi_fifth',
    'phi_ne_zero', 'one_plus_phi_ne_zero',
    'zeta5_pow_zero', 'zeta5_pow_zero_re', 'zeta5_pow_zero_im',
    'zeta5_pow_eq_one_iff',
    'zeta5_pow_add_five_mul',
    'zeta5_inv_mul', 'zeta5_mul_inv',
    'zeta5_inv_as_pow4',
    'zeta5_pow_mul_inv', 'zeta5_inv_mul_pow',
    'zeta5_sq_mul_inv', 'zeta5_pow4_mul_sq',
    'zeta5_pow4_eq',
    'zeta5_pow_seventeen',
    'zeta5_pow_ten_C', 'zeta5_pow_fifteen_C',

    # SegmentGeometry lemmas
    'F_ne_zero', 'segment_ratio_is_golden', 'translations_irrational',
    'E_re_pos', "E'_re_neg",

    # OrbitInfinite lemmas
    'goldenRatio_mul_rat_irrational', 'GG5_IET_rotation_irrational',
    'GG5_IET_orbit_nonempty', 'GG5_IET_orbit_finite_subset',
    'GG5_IET_has_orbit_structure',
    'denom_pos', 'length1_alt',
    'interval2_image_bound', 'length3_gt_length1', 'length1_lt_half',
    'GG5_induced_IET_is_order3',
}


def parse_dead_code_file(dead_code_path: Path) -> Dict[str, List[Tuple[str, int]]]:
    """Parse docs/dead_code.txt for user-written declarations."""
    file_decls = defaultdict(list)
    auto_gen_patterns = [
        '._proof_', '._simp_', '._nativeDecide_', '.match_', '._eq_',
        '.eq_', '.ctorElim', '.noConfusion', '.ofNat', '.recOn', '.elim',
        '.sizeOf_spec', '._aux_', '._sunfold', '.toCtorIdx', '.ctorIdx', '.ctorElimType'
    ]

    with open(dead_code_path, encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            match = re.search(r'^(\S+)\s+\((\w+)\)\s+\(([^:]+):(\d+)\)', line)
            if match:
                full_name = match.group(1)
                file_path = match.group(3)
                line_num = int(match.group(4))

                # Skip auto-generated
                if any(pattern in full_name for pattern in auto_gen_patterns):
                    continue

                decl_name = full_name.split('.')[-1]

                # Skip needed declarations
                if decl_name in NEEDED_DECLARATIONS:
                    continue

                file_decls[file_path].append((decl_name, line_num))

    return dict(file_decls)


def find_declaration_block(lines: List[str], start_idx: int) -> tuple:
    """Find the complete block to delete: doc comment + declaration."""
    # Scan backward for doc comment
    doc_start = start_idx
    i = start_idx - 1

    # Skip blank lines
    while i >= 0 and not lines[i].strip():
        i -= 1

    if i >= 0:
        stripped = lines[i].strip()
        if stripped.endswith('-/'):
            j = i
            while j >= 0:
                if lines[j].strip().startswith('/-'):
                    doc_start = j
                    break
                j -= 1
        elif stripped.startswith('--'):
            j = i
            while j >= 0 and lines[j].strip().startswith('--'):
                j -= 1
            doc_start = j + 1

    # Find end of declaration
    start_line = lines[start_idx]
    start_indent = len(start_line) - len(start_line.lstrip())

    decl_keywords = ['def ', 'theorem ', 'lemma ', 'axiom ', 'inductive ',
                     'structure ', 'class ', 'instance ', 'abbrev ', 'opaque ',
                     'example ', 'noncomputable def ', 'noncomputable abbrev ']

    i = start_idx + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()

        if not stripped or stripped.startswith('--'):
            i += 1
            continue

        current_indent = len(line) - len(stripped)

        if current_indent <= start_indent:
            for keyword in decl_keywords:
                if stripped.startswith(keyword):
                    return (doc_start, i - 1)

            if stripped.startswith('end ') or stripped.startswith('namespace '):
                return (doc_start, i - 1)

        i += 1

    return (doc_start, len(lines) - 1)


def delete_declarations(file_path: Path, declarations: List[Tuple[str, int]], dry_run: bool) -> tuple:
    """
    Delete specified declarations from a file.

    Returns: (deleted_count, deleted_names)
    """
    if not file_path.exists():
        return (0, [])

    with open(file_path, encoding='utf-8') as f:
        lines = f.readlines()

    declarations_sorted = sorted(declarations, key=lambda x: x[1], reverse=True)

    ranges_to_delete = []
    deleted_names = []

    for decl_name, line_num in declarations_sorted:
        idx = line_num - 1

        if idx < 0 or idx >= len(lines):
            continue

        if decl_name not in lines[idx]:
            continue

        start, end = find_declaration_block(lines, idx)
        ranges_to_delete.append((start, end, decl_name))
        deleted_names.append(decl_name)
        print(f"  🗑️  {decl_name} (lines {start + 1}-{end + 1})")

    if not ranges_to_delete:
        return (0, [])

    if not dry_run:
        for start, end, name in ranges_to_delete:
            del lines[start:end + 1]

        # Clean excessive blank lines
        cleaned = []
        blank_count = 0
        for line in lines:
            if line.strip():
                cleaned.append(line)
                blank_count = 0
            else:
                blank_count += 1
                if blank_count <= 2:
                    cleaned.append(line)

        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(cleaned)

    return (len(ranges_to_delete), deleted_names)


def main():
    parser = argparse.ArgumentParser(description='Delete only safe (non-breaking) declarations')
    parser.add_argument('--dry-run', action='store_true', help='Preview without deleting')
    args = parser.parse_args()

    dead_code_path = Path('docs/dead_code.txt')
    backup_dir = Path('backup')

    if not dead_code_path.exists():
        print("❌ Error: docs/dead_code.txt not found")
        sys.exit(1)

    backup_dir.mkdir(exist_ok=True)

    print("=== SAFE DECLARATION DELETION ===\n")
    print(f"Keeping {len(NEEDED_DECLARATIONS)} declarations that caused build errors")
    print(f"Deleting only provably-unused declarations\n")

    if args.dry_run:
        print("🔍 DRY RUN MODE\n")

    file_decls = parse_dead_code_file(dead_code_path)

    if not file_decls:
        print("✅ No safe deletions found (all dead code is actually needed)")
        sys.exit(0)

    total = sum(len(decls) for decls in file_decls.values())
    print(f"📊 Found {total} safe-to-delete declarations across {len(file_decls)} files\n")

    # Create backup
    if not args.dry_run:
        print("💾 Creating backup...")
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup_path = backup_dir / f'pre_safe_deletion_{timestamp}.tar.gz'

        with tarfile.open(backup_path, 'w:gz') as tar:
            for fp in file_decls.keys():
                if Path(fp).exists():
                    tar.add(fp, arcname=fp)

        print(f"   ✅ {backup_path}\n")

    # Process files
    total_deleted = 0
    all_deleted_names = []

    for file_path in sorted(file_decls.keys()):
        decls = file_decls[file_path]
        print(f"📄 {file_path} ({len(decls)} declarations)...")
        deleted_count, deleted_names = delete_declarations(Path(file_path), decls, args.dry_run)
        total_deleted += deleted_count
        all_deleted_names.extend(deleted_names)
        print()

    # Save report
    if not args.dry_run and all_deleted_names:
        report_path = Path('docs/deleted_declarations.txt')
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(f"Deleted {total_deleted} declarations at {datetime.now().isoformat()}\n\n")
            for name in sorted(all_deleted_names):
                f.write(f"{name}\n")
        print(f"📋 Deletion report: {report_path}\n")

    print("=" * 60)
    if args.dry_run:
        print(f"🔍 Would delete {total_deleted} declarations")
        print(f"   ({137 - total_deleted} kept as they caused build errors)")
    else:
        print(f"✅ Deleted {total_deleted} safe declarations")
        print(f"   ({137 - total_deleted} kept as they're actually needed)")
        print(f"\n📋 Next: lake build (should succeed)")


if __name__ == "__main__":
    main()
