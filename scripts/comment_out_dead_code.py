#!/usr/bin/env python3
"""
Comment out dead code declarations for build-based verification.

This script non-destructively comments out user-written declarations
marked as dead in docs/dead_code.txt, creating backups and tracking
for later restoration or deletion.
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
    """
    Parse docs/dead_code.txt to extract user-written declarations with file locations.

    Returns: Dict[file_path, List[(decl_name, line_number)]]
    Excludes auto-generated declarations (._proof_*, ._simp_*, etc.)
    """
    file_decls = defaultdict(list)
    auto_gen_patterns = [
        '._proof_', '._simp_', '._nativeDecide_', '.match_', '._eq_',
        '.eq_', '.ctorElim', '.noConfusion', '.ofNat', '.recOn', '.elim',
        '.sizeOf_spec', '._aux_', '._sunfold', '.toCtorIdx', '.ctorIdx', '.ctorElimType'
    ]

    with open(dead_code_path, encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            # Look for pattern: NAME (kind) (file:line)
            match = re.search(r'^(\S+)\s+\((\w+)\)\s+\(([^:]+):(\d+)\)', line)
            if match:
                full_name = match.group(1)
                kind = match.group(2)
                file_path = match.group(3)
                line_num = int(match.group(4))

                # Skip auto-generated declarations
                if any(pattern in full_name for pattern in auto_gen_patterns):
                    continue

                # Extract just the declaration name (last component)
                decl_name = full_name.split('.')[-1]
                file_decls[file_path].append((decl_name, line_num))

    return dict(file_decls)


def find_doc_comment_start(lines: List[str], decl_line: int) -> int:
    """
    Scan backward from declaration line to find start of doc comment.
    Returns the line index where commenting should start (inclusive).
    """
    # Start from line before declaration
    i = decl_line - 1
    doc_start = decl_line  # Default: no doc comment

    # Skip blank lines
    while i >= 0 and not lines[i].strip():
        i -= 1

    if i < 0:
        return decl_line

    # Check for single-line or multi-line doc comment
    stripped = lines[i].strip()

    # Multi-line doc comment ending
    if stripped.endswith('-/'):
        # Find start of multi-line comment
        j = i
        while j >= 0:
            if lines[j].strip().startswith('/-'):
                return j
            j -= 1
        return i  # Shouldn't happen, but be safe

    # Single-line doc comment
    elif stripped.startswith('--'):
        # Collect all consecutive single-line comments
        j = i
        while j >= 0 and lines[j].strip().startswith('--'):
            j -= 1
        return j + 1

    return decl_line


def find_declaration_end(lines: List[str], start_idx: int, decl_name: str) -> int:
    """
    Find where a declaration ends by looking for the next top-level declaration.

    Returns: Index of last line belonging to this declaration (inclusive)
    """
    # Get the indentation level of the declaration
    start_line = lines[start_idx]
    start_indent = len(start_line) - len(start_line.lstrip())

    # Keywords that mark top-level declarations at same or lower indentation
    decl_keywords = ['def ', 'theorem ', 'lemma ', 'axiom ', 'inductive ',
                     'structure ', 'class ', 'instance ', 'abbrev ', 'opaque ',
                     'example ', 'noncomputable def ', 'noncomputable abbrev ']

    # Scan forward to find the end
    i = start_idx + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()

        # Skip empty lines and comments
        if not stripped or stripped.startswith('--'):
            i += 1
            continue

        # Check indentation
        current_indent = len(line) - len(stripped)

        # If we're back at same or lower indentation and hit a declaration keyword
        if current_indent <= start_indent:
            for keyword in decl_keywords:
                if stripped.startswith(keyword):
                    # Found next declaration, return previous line
                    return i - 1

            # Check for namespace or section ends
            if stripped.startswith('end ') or stripped.startswith('namespace '):
                return i - 1

        i += 1

    # Reached end of file
    return len(lines) - 1


def comment_out_region(lines: List[str], start: int, end: int, name: str) -> List[str]:
    """
    Comment out lines[start:end+1] with line-by-line commenting.

    Returns: Modified lines with region commented out.
    """
    result = []

    # Add marker comment
    indent = len(lines[start]) - len(lines[start].lstrip())
    marker = ' ' * indent + f'-- DEAD CODE TEST: {name}\n'
    result.append(marker)

    # Comment out each line
    for i in range(start, end + 1):
        line = lines[i]
        # Preserve indentation, add -- before content
        stripped = line.lstrip()
        if stripped:  # Non-empty line
            indent_size = len(line) - len(stripped)
            commented = ' ' * indent_size + '-- ' + stripped
            result.append(commented)
        else:  # Empty line
            result.append(line)

    return result


def create_backup(files: List[Path], backup_dir: Path) -> Path:
    """
    Create tarball backup of files before modification.

    Returns: Path to backup tarball
    """
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    backup_path = backup_dir / f'original_files_{timestamp}.tar.gz'

    with tarfile.open(backup_path, 'w:gz') as tar:
        for file_path in files:
            if file_path.exists():
                tar.add(file_path, arcname=str(file_path))

    return backup_path


def process_file(file_path: Path, declarations: List[Tuple[str, int]], dry_run: bool, verbose: bool) -> Dict:
    """
    Comment out specified declarations in a file.

    Returns: Modification tracking data for this file
    """
    if not file_path.exists():
        print(f"  ⚠️  File not found: {file_path}")
        return None

    # Read file
    with open(file_path, encoding='utf-8') as f:
        lines = f.readlines()

    # Sort declarations by line number (descending) to process bottom-up
    declarations_sorted = sorted(declarations, key=lambda x: x[1], reverse=True)

    modifications = []

    for decl_name, line_num in declarations_sorted:
        # Convert to 0-indexed
        idx = line_num - 1

        if idx < 0 or idx >= len(lines):
            if verbose:
                print(f"  ⚠️  Invalid line number {line_num} for {decl_name}")
            continue

        # Verify this line contains the declaration
        line = lines[idx]
        if decl_name not in line:
            if verbose:
                print(f"  ⚠️  Declaration {decl_name} not found at line {line_num}")
            continue

        # Find declaration end (don't include doc comments)
        decl_end = find_declaration_end(lines, idx, decl_name)

        # Track modification
        mod = {
            'name': decl_name,
            'line': line_num,
            'start_line': idx + 1,  # Back to 1-indexed (declaration start, not doc comment)
            'end_line': decl_end + 1,
            'commented': not dry_run
        }
        modifications.append(mod)

        if verbose:
            print(f"  🔨 {decl_name} (lines {line_num}-{decl_end + 1})")

        if not dry_run:
            # Comment out the region (declaration only, not doc comment)
            commented = comment_out_region(lines, idx, decl_end, decl_name)

            # Replace in lines array
            lines[idx:decl_end + 1] = commented

    # Write back if not dry run
    if not dry_run and modifications:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)

    return {
        'path': str(file_path),
        'declarations': modifications
    }


def main():
    parser = argparse.ArgumentParser(description='Comment out dead code for build testing')
    parser.add_argument('--dry-run', action='store_true', help='Preview changes without modifying files')
    parser.add_argument('--verbose', action='store_true', help='Verbose output')
    args = parser.parse_args()

    # Paths
    dead_code_path = Path('docs/dead_code.txt')
    backup_dir = Path('backup')

    if not dead_code_path.exists():
        print("❌ Error: docs/dead_code.txt not found")
        print("Run 'lake exe find_dead_code' first")
        sys.exit(1)

    backup_dir.mkdir(exist_ok=True)

    print("=== DEAD CODE COMMENT-OUT (Build Verification) ===\n")

    if args.dry_run:
        print("🔍 DRY RUN MODE - No files will be modified\n")

    print("📖 Reading dead code analysis...")
    file_decls = parse_dead_code_file(dead_code_path)

    if not file_decls:
        print("✅ No user-written dead code with file locations found")
        sys.exit(0)

    total_files = len(file_decls)
    total_decls = sum(len(decls) for decls in file_decls.values())

    print(f"📊 Found {total_decls} user-written declarations across {total_files} files")
    print(f"   (Excluded auto-generated auxiliaries: ._proof_*, ._simp_*, etc.)\n")

    # Create backup before modification
    if not args.dry_run:
        print("💾 Creating backup...")
        files_to_backup = [Path(fp) for fp in file_decls.keys() if Path(fp).exists()]
        backup_path = create_backup(files_to_backup, backup_dir)
        print(f"   ✅ Backup: {backup_path}\n")

    # Process each file
    all_modifications = []
    modified_count = 0

    for file_path in sorted(file_decls.keys()):
        decls = file_decls[file_path]
        print(f"📄 {file_path} ({len(decls)} declarations)...")

        mod_data = process_file(Path(file_path), decls, args.dry_run, args.verbose)
        if mod_data and mod_data['declarations']:
            all_modifications.append(mod_data)
            modified_count += 1
        print()

    # Save tracking file
    if not args.dry_run:
        tracking_path = backup_dir / 'commented_declarations.json'
        tracking_data = {
            'timestamp': datetime.now().isoformat(),
            'total_files': total_files,
            'total_declarations': total_decls,
            'files_modified': all_modifications
        }

        with open(tracking_path, 'w', encoding='utf-8') as f:
            json.dump(tracking_data, f, indent=2)

        print(f"📋 Tracking file: {tracking_path}")

    print("=" * 60)

    if args.dry_run:
        print(f"🔍 DRY RUN COMPLETE: Would modify {modified_count}/{total_files} files")
        print(f"\nRun without --dry-run to apply changes")
    else:
        print(f"✅ COMPLETE: Modified {modified_count}/{total_files} files")
        print(f"\n📋 Next steps:")
        print(f"  1. Run: python scripts/build_and_parse_errors.py")
        print(f"  2. This will identify which declarations are actually needed")
        print(f"  3. Rollback: tar -xzf {backup_path}")


if __name__ == "__main__":
    main()
