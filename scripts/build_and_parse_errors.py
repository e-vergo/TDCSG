#!/usr/bin/env python3
"""
Build the project and parse errors to identify needed declarations.

This script runs `lake build` after declarations have been commented out,
parses the build errors to identify which declarations are actually needed,
and creates a list for restoration.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Set
from collections import defaultdict


def run_lake_build(timeout=600) -> tuple:
    """
    Run lake build and capture output.

    Returns: (returncode, stdout, stderr)
    """
    print("🔨 Running lake build...")
    print("   (This may take a few minutes...)\n")

    try:
        result = subprocess.run(
            ['lake', 'build'],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        return (result.returncode, result.stdout, result.stderr)
    except subprocess.TimeoutExpired:
        print(f"⚠️  Build timed out after {timeout}s")
        return (-1, "", "Build timeout")
    except Exception as e:
        print(f"❌ Error running build: {e}")
        return (-1, "", str(e))


def parse_error_log(log_content: str) -> List[Dict]:
    """
    Parse build errors to extract missing declaration information.

    Returns: List of error dictionaries
    """
    errors = []

    # Error patterns to match
    patterns = [
        # unknown identifier 'name'
        (r"unknown identifier '([^']+)'", 'unknown_identifier'),
        # unknown constant 'name'
        (r"unknown constant '([^']+)'", 'unknown_constant'),
        # failed to synthesize with name mentioned
        (r"failed to synthesize[^']*'([^']+)'", 'failed_synthesize'),
        # application type mismatch mentioning names
        (r"application type mismatch[^']*'([^']+)'", 'type_mismatch'),
        # expected ... but got ... with name
        (r"expected[^']*'([^']+)'", 'type_expected'),
    ]

    # Track file context for errors
    current_file = None
    file_pattern = r"error: ([^:]+\.lean):(\d+):(\d+):"

    for line in log_content.split('\n'):
        # Track which file we're in
        file_match = re.search(file_pattern, line)
        if file_match:
            current_file = file_match.group(1)
            line_num = file_match.group(2)
            col_num = file_match.group(3)

        # Check for error patterns
        for pattern, error_type in patterns:
            matches = re.findall(pattern, line)
            for match in matches:
                errors.append({
                    'type': error_type,
                    'name': match,
                    'file': current_file or 'unknown',
                    'message': line.strip()
                })

    return errors


def extract_declaration_names(errors: List[Dict]) -> Set[str]:
    """
    Extract unique declaration names from errors.

    Returns: Set of declaration names that caused errors
    """
    names = set()
    for error in errors:
        name = error['name']
        # Extract just the base name (last component after '.')
        if '.' in name:
            name = name.split('.')[-1]
        names.add(name)
    return names


def cross_reference_with_tracking(needed_names: Set[str], tracking_path: Path) -> List[Dict]:
    """
    Cross-reference needed names with commented declarations tracking file.

    Returns: List of declarations that need to be restored
    """
    if not tracking_path.exists():
        print(f"⚠️  Tracking file not found: {tracking_path}")
        return []

    with open(tracking_path, encoding='utf-8') as f:
        tracking_data = json.load(f)

    needed_declarations = []

    for file_data in tracking_data['files_modified']:
        for decl in file_data['declarations']:
            if decl['name'] in needed_names:
                needed_declarations.append({
                    'name': decl['name'],
                    'file': file_data['path'],
                    'line': decl['line'],
                    'start_line': decl['start_line'],
                    'end_line': decl['end_line']
                })

    return needed_declarations


def save_needed_declarations(needed_decls: List[Dict], errors: List[Dict], output_path: Path, returncode: int):
    """
    Save list of needed declarations and error context to JSON.
    """
    # Group errors by declaration name
    errors_by_name = defaultdict(list)
    for error in errors:
        name = error['name']
        if '.' in name:
            name = name.split('.')[-1]
        errors_by_name[name].append(f"{error['type']} in {error['file']}: {error['message'][:80]}")

    # Add error context to declarations
    for decl in needed_decls:
        decl['errors'] = errors_by_name.get(decl['name'], [])

    output_data = {
        'timestamp': datetime.now().isoformat(),
        'build_status': 'failed' if returncode != 0 else 'success',
        'error_count': len(errors),
        'unique_missing_names': len(set(e['name'] for e in errors)),
        'needed_declarations_count': len(needed_decls),
        'needed_declarations': needed_decls
    }

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output_data, f, indent=2)


def main():
    parser = argparse.ArgumentParser(description='Build and parse errors to identify needed declarations')
    parser.add_argument('--log', default='build_errors.log', help='Path to save build log')
    parser.add_argument('--timeout', type=int, default=600, help='Build timeout in seconds')
    args = parser.parse_args()

    # Paths
    backup_dir = Path('backup')
    tracking_path = backup_dir / 'commented_declarations.json'
    log_path = Path(args.log)
    output_path = backup_dir / 'needed_declarations.json'

    if not tracking_path.exists():
        print("❌ Error: backup/commented_declarations.json not found")
        print("Run 'python scripts/comment_out_dead_code.py' first")
        sys.exit(1)

    print("=== BUILD AND ERROR ANALYSIS ===\n")

    # Run build
    returncode, stdout, stderr = run_lake_build(args.timeout)

    # Combine and save log
    log_content = stdout + "\n" + stderr
    with open(log_path, 'w', encoding='utf-8') as f:
        f.write(log_content)

    print(f"📋 Build log saved to: {log_path}")

    if returncode == 0:
        print("\n✅ BUILD SUCCEEDED")
        print("\nThis means all commented declarations are truly unused!")
        print("You can proceed to delete them with scripts/delete_truly_unused.py")

        # Still save the output file with empty needed list
        output_data = {
            'timestamp': datetime.now().isoformat(),
            'build_status': 'success',
            'error_count': 0,
            'needed_declarations_count': 0,
            'needed_declarations': []
        }
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(output_data, f, indent=2)

        print(f"📋 Results saved to: {output_path}")
        sys.exit(0)

    print(f"\n❌ BUILD FAILED (exit code: {returncode})")
    print("\nParsing errors to identify needed declarations...\n")

    # Parse errors
    errors = parse_error_log(log_content)
    print(f"📊 Found {len(errors)} error messages")

    if not errors:
        print("\n⚠️  No parseable errors found in build output")
        print("Check build_errors.log manually")
        sys.exit(1)

    # Extract names
    needed_names = extract_declaration_names(errors)
    print(f"📊 Identified {len(needed_names)} unique missing declaration names")

    # Cross-reference with tracking
    needed_decls = cross_reference_with_tracking(needed_names, tracking_path)
    print(f"📊 Matched {len(needed_decls)} declarations from commented set")

    # Save results
    save_needed_declarations(needed_decls, errors, output_path, returncode)
    print(f"\n📋 Results saved to: {output_path}")

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY:")
    print(f"  Build status: FAILED")
    print(f"  Total errors: {len(errors)}")
    print(f"  Missing declarations: {len(needed_names)}")
    print(f"  To restore: {len(needed_decls)}")

    if needed_decls:
        print(f"\n📋 Top 10 needed declarations:")
        for decl in needed_decls[:10]:
            print(f"  - {decl['name']} ({decl['file']}:{decl['line']})")

    print(f"\n📋 Next step:")
    print(f"  python scripts/restore_needed_declarations.py")


if __name__ == "__main__":
    main()
