#!/usr/bin/env python3
"""
Simple approach: Delete dead code declarations directly.

Simpler than commenting - just delete the declarations and their doc comments.
We have git backup, so can restore if needed.
"""

import argparse
import json
import re
import sys
import tarfile
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple
from collections import defaultdict


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
                file_decls[file_path].append((decl_name, line_num))

    return dict(file_decls)


def find_declaration_block(lines: List[str], start_idx: int) -> tuple:
    """
    Find the complete block to delete: doc comment + declaration.
    Returns: (start_line, end_line) inclusive
    """
    # Scan backward for doc comment
    doc_start = start_idx
    i = start_idx - 1

    # Skip blank lines
    while i >= 0 and not lines[i].strip():
        i -= 1

    if i >= 0:
        stripped = lines[i].strip()
        # Multi-line doc comment ending
        if stripped.endswith('-/'):
            j = i
            while j >= 0:
                if lines[j].strip().startswith('/-'):
                    doc_start = j
                    break
                j -= 1
        # Single-line doc comments
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


def delete_declarations(file_path: Path, declarations: List[Tuple[str, int]], dry_run: bool) -> int:
    """Delete specified declarations from a file."""
    if not file_path.exists():
        print(f"  ⚠️  File not found: {file_path}")
        return 0

    with open(file_path, encoding='utf-8') as f:
        lines = f.readlines()

    # Sort by line (descending) to delete bottom-up
    declarations_sorted = sorted(declarations, key=lambda x: x[1], reverse=True)

    # Collect ranges to delete
    ranges_to_delete = []

    for decl_name, line_num in declarations_sorted:
        idx = line_num - 1

        if idx < 0 or idx >= len(lines):
            continue

        if decl_name not in lines[idx]:
            continue

        start, end = find_declaration_block(lines, idx)
        ranges_to_delete.append((start, end, decl_name))
        print(f"  🗑️  {decl_name} (lines {start + 1}-{end + 1})")

    if not ranges_to_delete:
        return 0

    # Delete ranges (bottom-up, so indices don't shift)
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

    return len(ranges_to_delete)


def main():
    parser = argparse.ArgumentParser(description='Delete dead code declarations')
    parser.add_argument('--dry-run', action='store_true', help='Preview without deleting')
    args = parser.parse_args()

    dead_code_path = Path('docs/dead_code.txt')
    backup_dir = Path('backup')

    if not dead_code_path.exists():
        print("❌ Error: docs/dead_code.txt not found")
        sys.exit(1)

    backup_dir.mkdir(exist_ok=True)

    print("=== DEAD CODE DELETION (Direct Approach) ===\n")
    if args.dry_run:
        print("🔍 DRY RUN MODE\n")

    file_decls = parse_dead_code_file(dead_code_path)

    if not file_decls:
        print("✅ No dead code found")
        sys.exit(0)

    total = sum(len(decls) for decls in file_decls.values())
    print(f"📊 Found {total} declarations across {len(file_decls)} files\n")

    # Create backup
    if not args.dry_run:
        print("💾 Creating backup...")
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup_path = backup_dir / f'pre_deletion_{timestamp}.tar.gz'

        with tarfile.open(backup_path, 'w:gz') as tar:
            for fp in file_decls.keys():
                if Path(fp).exists():
                    tar.add(fp, arcname=fp)

        print(f"   ✅ {backup_path}\n")

    # Process files
    total_deleted = 0
    for file_path in sorted(file_decls.keys()):
        decls = file_decls[file_path]
        print(f"📄 {file_path} ({len(decls)} declarations)...")
        deleted = delete_declarations(Path(file_path), decls, args.dry_run)
        total_deleted += deleted
        print()

    print("=" * 60)
    if args.dry_run:
        print(f"🔍 Would delete {total_deleted} declarations")
    else:
        print(f"✅ Deleted {total_deleted} declarations")
        print(f"\n📋 Next: lake build")


if __name__ == "__main__":
    main()
