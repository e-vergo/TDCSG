#!/usr/bin/env python3
"""
Restore declarations that broke the build.

This script uncomments declarations that were identified as needed
by the build error analysis, allowing the build to succeed.
"""

import argparse
import json
import re
import sys
from pathlib import Path
from datetime import datetime
from typing import List, Dict
from collections import defaultdict


def load_needed_declarations(needed_path: Path) -> List[Dict]:
    """
    Load list of needed declarations from JSON.

    Returns: List of declaration dictionaries
    """
    with open(needed_path, encoding='utf-8') as f:
        data = json.load(f)
    return data['needed_declarations']


def load_tracking_manifest(tracking_path: Path) -> Dict:
    """
    Load tracking manifest.

    Returns: Tracking data dictionary
    """
    with open(tracking_path, encoding='utf-8') as f:
        return json.load(f)


def find_comment_markers(lines: List[str], decl_name: str, start_hint: int) -> tuple:
    """
    Find the comment markers for a specific declaration.

    Returns: (opening_line_idx, closing_line_idx) or (None, None) if not found
    """
    # Search around the hint line
    search_start = max(0, start_hint - 5)
    search_end = min(len(lines), start_hint + 100)

    opening = None
    closing = None

    for i in range(search_start, search_end):
        line = lines[i]
        # Look for opening marker
        if f'-- DEAD CODE TEST: {decl_name}' in line:
            opening = i
            # Find the end of the commented region
            # It ends when we find a non-commented line at the same or lower indentation
            marker_indent = len(line) - len(line.lstrip())
            j = i + 1
            while j < len(lines):
                next_line = lines[j]
                next_stripped = next_line.lstrip()

                # Check if this line is commented or empty
                if not next_stripped or next_stripped.startswith('--'):
                    j += 1
                    continue

                # Found uncommented line, end of region is previous line
                closing = j - 1
                break

            if closing is None:
                # Reached end of file
                closing = len(lines) - 1
            break

    return (opening, closing)


def uncomment_region(lines: List[str], opening: int, closing: int) -> List[str]:
    """
    Remove line-by-line comment markers, restoring original code.

    Returns: Modified lines with comments removed
    """
    result = []

    for i, line in enumerate(lines):
        if i == opening:
            # Skip marker line
            continue
        elif i > opening and i <= closing:
            # Uncomment this line
            stripped = line.lstrip()
            if stripped.startswith('-- '):
                # Remove the '-- ' prefix, preserving indentation
                indent_size = len(line) - len(stripped)
                uncommented = ' ' * indent_size + stripped[3:]  # Remove '-- '
                result.append(uncommented)
            else:
                # Line wasn't commented (empty or something else), keep as-is
                result.append(line)
        else:
            # Not in commented region
            result.append(line)

    return result


def update_tracking(tracking_data: Dict, restored_names: List[str]) -> Dict:
    """
    Update tracking manifest to mark declarations as restored.

    Returns: Modified tracking data
    """
    for file_data in tracking_data['files_modified']:
        for decl in file_data['declarations']:
            if decl['name'] in restored_names:
                decl['commented'] = False
                decl['restored'] = True

    return tracking_data


def process_file(file_path: Path, declarations: List[Dict], verbose: bool) -> int:
    """
    Restore specified declarations in a file.

    Returns: Number of declarations restored
    """
    if not file_path.exists():
        print(f"  ⚠️  File not found: {file_path}")
        return 0

    # Read file
    with open(file_path, encoding='utf-8') as f:
        lines = f.readlines()

    restored_count = 0

    for decl in declarations:
        decl_name = decl['name']
        start_hint = decl['start_line'] - 1  # Convert to 0-indexed

        # Find comment markers
        opening, closing = find_comment_markers(lines, decl_name, start_hint)

        if opening is None or closing is None:
            if verbose:
                print(f"  ⚠️  Could not find markers for {decl_name}")
            continue

        if verbose:
            print(f"  ✅ Restoring {decl_name} (remove lines {opening + 1} and {closing + 1})")

        # Uncomment by removing markers
        lines = uncomment_region(lines, opening, closing)
        restored_count += 1

    # Write back
    if restored_count > 0:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)

    return restored_count


def main():
    parser = argparse.ArgumentParser(description='Restore needed declarations')
    parser.add_argument('--verify', action='store_true', help='Verify build succeeds after restoration')
    parser.add_argument('--verbose', action='store_true', help='Verbose output')
    args = parser.parse_args()

    # Paths
    backup_dir = Path('backup')
    needed_path = backup_dir / 'needed_declarations.json'
    tracking_path = backup_dir / 'commented_declarations.json'

    if not needed_path.exists():
        print("❌ Error: backup/needed_declarations.json not found")
        print("Run 'python scripts/build_and_parse_errors.py' first")
        sys.exit(1)

    if not tracking_path.exists():
        print("❌ Error: backup/commented_declarations.json not found")
        sys.exit(1)

    print("=== RESTORE NEEDED DECLARATIONS ===\n")

    # Load data
    needed_decls = load_needed_declarations(needed_path)

    if not needed_decls:
        print("✅ No declarations need to be restored (build already succeeded)")
        sys.exit(0)

    print(f"📊 Found {len(needed_decls)} declarations to restore\n")

    # Group by file
    decls_by_file = defaultdict(list)
    for decl in needed_decls:
        decls_by_file[decl['file']].append(decl)

    # Process each file
    total_restored = 0

    for file_path in sorted(decls_by_file.keys()):
        decls = decls_by_file[file_path]
        print(f"📄 {file_path} ({len(decls)} declarations)...")

        restored = process_file(Path(file_path), decls, args.verbose)
        total_restored += restored

        if not args.verbose:
            print(f"   ✅ Restored {restored} declarations")
        print()

    # Update tracking
    print("📝 Updating tracking manifest...")
    tracking_data = load_tracking_manifest(tracking_path)
    restored_names = [d['name'] for d in needed_decls]
    tracking_data = update_tracking(tracking_data, restored_names)

    with open(tracking_path, 'w', encoding='utf-8') as f:
        json.dump(tracking_data, f, indent=2)

    print("=" * 60)
    print(f"✅ COMPLETE: Restored {total_restored} declarations")

    # Verify build if requested
    if args.verify:
        print("\n🔨 Verifying build...")
        import subprocess

        try:
            result = subprocess.run(['lake', 'build'], capture_output=True, text=True, timeout=600)

            if result.returncode == 0:
                print("✅ Build succeeded!")
                print("\n📋 Next step:")
                print("  python scripts/delete_truly_unused.py")
            else:
                print("❌ Build still fails")
                print("There may be additional needed declarations not detected.")
                print("Check build errors manually.")
                sys.exit(1)

        except Exception as e:
            print(f"⚠️  Could not verify build: {e}")
            sys.exit(1)
    else:
        print("\n📋 Next steps:")
        print("  1. Run: lake build")
        print("  2. If build succeeds:")
        print("     python scripts/delete_truly_unused.py")
        print("  3. If build fails:")
        print("     Review errors - may need manual intervention")


if __name__ == "__main__":
    main()
