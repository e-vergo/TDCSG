#!/usr/bin/env python3
"""
Delete declarations that are truly unused (didn't break the build).

This script deletes declarations that remained commented after restoration,
meaning they didn't break the build and are truly unused.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import List, Dict
from collections import defaultdict


def verify_build_succeeds(timeout=600) -> bool:
    """
    Verify that lake build succeeds.

    Returns: True if build succeeds, False otherwise
    """
    print("🔨 Verifying build status...")

    try:
        result = subprocess.run(
            ['lake', 'build'],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        if result.returncode == 0:
            print("   ✅ Build succeeds\n")
            return True
        else:
            print("   ❌ Build fails\n")
            return False

    except Exception as e:
        print(f"   ⚠️  Error running build: {e}\n")
        return False


def load_still_commented(tracking_path: Path) -> List[Dict]:
    """
    Load declarations that are still commented (not restored).

    Returns: List of declaration dictionaries grouped by file
    """
    with open(tracking_path, encoding='utf-8') as f:
        tracking_data = json.load(f)

    still_commented = []

    for file_data in tracking_data['files_modified']:
        file_decls = []
        for decl in file_data['declarations']:
            if decl.get('commented', False) and not decl.get('restored', False):
                file_decls.append(decl)

        if file_decls:
            still_commented.append({
                'path': file_data['path'],
                'declarations': file_decls
            })

    return still_commented


def find_comment_region(lines: List[str], decl_name: str, start_hint: int) -> tuple:
    """
    Find the commented region for a declaration.

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


def delete_commented_region(lines: List[str], opening: int, closing: int) -> List[str]:
    """
    Delete the commented region entirely.

    Returns: Modified lines with region removed
    """
    # Delete everything from opening to closing (inclusive)
    result = []

    for i, line in enumerate(lines):
        if i < opening or i > closing:
            result.append(line)

    return result


def clean_blank_lines(lines: List[str]) -> List[str]:
    """
    Remove excessive blank lines (max 2 consecutive).

    Returns: Cleaned lines
    """
    result = []
    blank_count = 0

    for line in lines:
        if line.strip():
            result.append(line)
            blank_count = 0
        else:
            blank_count += 1
            if blank_count <= 2:
                result.append(line)

    return result


def process_file(file_path: Path, declarations: List[Dict], dry_run: bool, verbose: bool) -> int:
    """
    Delete specified declarations from a file.

    Returns: Number of declarations deleted
    """
    if not file_path.exists():
        print(f"  ⚠️  File not found: {file_path}")
        return 0

    # Read file
    with open(file_path, encoding='utf-8') as f:
        lines = f.readlines()

    # Sort by line number (descending) to delete bottom-up
    declarations_sorted = sorted(declarations, key=lambda x: x['start_line'], reverse=True)

    deleted_count = 0

    for decl in declarations_sorted:
        decl_name = decl['name']
        start_hint = decl['start_line'] - 1  # Convert to 0-indexed

        # Find comment region
        opening, closing = find_comment_region(lines, decl_name, start_hint)

        if opening is None or closing is None:
            if verbose:
                print(f"  ⚠️  Could not find commented region for {decl_name}")
            continue

        if verbose:
            print(f"  🗑️  Deleting {decl_name} (lines {opening + 1}-{closing + 1})")

        # Delete the region
        lines = delete_commented_region(lines, opening, closing)
        deleted_count += 1

    # Clean up excessive blank lines
    if deleted_count > 0:
        lines = clean_blank_lines(lines)

        if not dry_run:
            # Write back
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(lines)

    return deleted_count


def create_deletion_report(deleted_files: List[Dict], output_path: Path):
    """
    Create a report of deleted declarations.
    """
    report_data = {
        'timestamp': datetime.now().isoformat(),
        'total_files_modified': len(deleted_files),
        'total_declarations_deleted': sum(len(f['declarations']) for f in deleted_files),
        'deleted_by_file': deleted_files
    }

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(report_data, f, indent=2)


def run_final_verifications(skip_verify: bool) -> tuple:
    """
    Run final verification checks.

    Returns: (build_ok, km_ok, deadcode_status)
    """
    print("\n=== FINAL VERIFICATION ===\n")

    if skip_verify:
        print("⚠️  Skipping verification checks (--skip-verify)\n")
        return (None, None, None)

    # 1. Build check
    print("1. Running lake build...")
    try:
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True, timeout=600)
        build_ok = result.returncode == 0
        print(f"   {'✅' if build_ok else '❌'} Build: {'PASS' if build_ok else 'FAIL'}")
    except Exception as e:
        print(f"   ⚠️  Could not run build: {e}")
        build_ok = False

    # 2. KM Standard check
    print("\n2. Running KMVerify...")
    try:
        result = subprocess.run(['lake', 'env', 'lean', '--run', 'KMVerify/Main.lean'],
                              capture_output=True, text=True, timeout=300)
        km_ok = 'PROJECT VERIFIED' in result.stdout
        print(f"   {'✅' if km_ok else '❌'} KMVerify: {'PASS' if km_ok else 'FAIL'}")
    except Exception as e:
        print(f"   ⚠️  Could not run KMVerify: {e}")
        km_ok = False

    # 3. Dead code check
    print("\n3. Running find_dead_code...")
    try:
        result = subprocess.run(['lake', 'exe', 'find_dead_code'],
                              capture_output=True, text=True, timeout=300)
        # Parse output to check dead code count
        if 'Dead code:' in result.stderr:
            match = re.search(r'Dead code: (\d+)', result.stderr)
            if match:
                dead_count = int(match.group(1))
                print(f"   {'✅' if dead_count == 0 else '⚠️'} Dead code: {dead_count} declarations")
                deadcode_status = dead_count
            else:
                print("   ⚠️  Could not parse dead code count")
                deadcode_status = -1
        else:
            print("   ⚠️  Could not run find_dead_code")
            deadcode_status = -1
    except Exception as e:
        print(f"   ⚠️  Could not run find_dead_code: {e}")
        deadcode_status = -1

    return (build_ok, km_ok, deadcode_status)


def main():
    parser = argparse.ArgumentParser(description='Delete truly unused declarations')
    parser.add_argument('--dry-run', action='store_true', help='Preview deletions without modifying files')
    parser.add_argument('--skip-verify', action='store_true', help='Skip final verification checks')
    parser.add_argument('--verbose', action='store_true', help='Verbose output')
    args = parser.parse_args()

    # Paths
    backup_dir = Path('backup')
    tracking_path = backup_dir / 'commented_declarations.json'
    report_path = Path('docs/deleted_declarations.txt')

    if not tracking_path.exists():
        print("❌ Error: backup/commented_declarations.json not found")
        sys.exit(1)

    print("=== DELETE TRULY UNUSED DECLARATIONS ===\n")

    if args.dry_run:
        print("🔍 DRY RUN MODE - No files will be modified\n")

    # Verify build succeeds before deletion
    if not args.dry_run and not args.skip_verify:
        if not verify_build_succeeds():
            print("❌ Build must succeed before deletion")
            print("Run 'python scripts/restore_needed_declarations.py' first")
            sys.exit(1)

    # Load declarations still commented
    still_commented = load_still_commented(tracking_path)

    if not still_commented:
        print("✅ No declarations to delete (all were needed)\n")

        # Still run verification
        if not args.skip_verify:
            run_final_verifications(args.skip_verify)

        sys.exit(0)

    total_decls = sum(len(f['declarations']) for f in still_commented)
    print(f"📊 Found {total_decls} declarations across {len(still_commented)} files to delete\n")

    # Process each file
    deleted_files = []
    total_deleted = 0

    for file_data in still_commented:
        file_path = Path(file_data['path'])
        decls = file_data['declarations']

        print(f"📄 {file_path} ({len(decls)} declarations)...")

        deleted = process_file(file_path, decls, args.dry_run, args.verbose)
        total_deleted += deleted

        if deleted > 0:
            deleted_files.append({
                'path': str(file_path),
                'declarations': [d['name'] for d in decls]
            })

        if not args.verbose:
            print(f"   {'🔍' if args.dry_run else '✅'} {'Would delete' if args.dry_run else 'Deleted'} {deleted} declarations")
        print()

    print("=" * 60)

    if args.dry_run:
        print(f"🔍 DRY RUN COMPLETE: Would delete {total_deleted} declarations")
        print(f"\nRun without --dry-run to apply deletions")
        sys.exit(0)

    print(f"✅ DELETION COMPLETE: Deleted {total_deleted} declarations\n")

    # Create report
    if deleted_files:
        create_deletion_report(deleted_files, report_path)
        print(f"📋 Deletion report: {report_path}\n")

    # Run final verifications
    build_ok, km_ok, deadcode_status = run_final_verifications(args.skip_verify)

    # Summary
    print("\n" + "=" * 60)
    print("FINAL STATUS:")

    if not args.skip_verify:
        print(f"  Build: {'✅ PASS' if build_ok else '❌ FAIL'}")
        print(f"  KMVerify: {'✅ PASS' if km_ok else '❌ FAIL'}")
        print(f"  Dead code: {deadcode_status if deadcode_status != -1 else 'UNKNOWN'}")

        if build_ok and km_ok:
            print("\n✅ All verifications passed!")
            print("\n📋 Next steps:")
            print("  1. bash scripts/build_dep_graph.sh")
            print("  2. Update README.md with new statistics")
            print("  3. git add -A && git commit -m 'Remove build-verified dead code'")
        else:
            print("\n❌ Some verifications failed")
            print("Review the issues before committing")
            sys.exit(1)
    else:
        print(f"  Declarations deleted: {total_deleted}")
        print("\n⚠️  Verification skipped - run checks manually")


if __name__ == "__main__":
    main()
