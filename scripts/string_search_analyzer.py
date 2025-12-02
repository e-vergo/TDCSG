#!/usr/bin/env python3
"""
String-based dead code analyzer for Lean 4.

Two modes:
1. --generate-report: Analyze declarations and generate editable report
2. --execute-deletions: Read report and delete declarations marked DELETE

Usage:
    python scripts/string_search_analyzer.py --generate-report
    python scripts/string_search_analyzer.py --execute-deletions [--dry-run]
"""

import argparse
import re
import sys
import tarfile
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Set


# Auto-generated patterns to skip (from existing scripts)
AUTO_GEN_PATTERNS = [
    '._proof_', '._simp_', '._nativeDecide_', '.match_', '._eq_',
    '.eq_', '.ctorElim', '.noConfusion', '.ofNat', '.recOn', '.elim',
    '.sizeOf_spec', '._aux_', '._sunfold', '.toCtorIdx', '.ctorIdx', '.ctorElimType'
]


def parse_dead_code_file(dead_code_path: Path) -> Dict[str, List[Tuple[str, int, str]]]:
    """
    Parse docs/dead_code.txt for user-written declarations.

    Returns: Dict[file_path, List[(short_name, line_num, full_name)]]
    """
    file_decls = defaultdict(list)

    with open(dead_code_path, encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            # Match format: FULL_NAME (kind) (file:line)
            match = re.search(r'^(\S+)\s+\((\w+)\)\s+\(([^:]+):(\d+)\)', line)
            if match:
                full_name = match.group(1)
                file_path = match.group(3)
                line_num = int(match.group(4))

                # Skip auto-generated
                if any(pattern in full_name for pattern in AUTO_GEN_PATTERNS):
                    continue

                # Extract short name (last component)
                short_name = full_name.split('.')[-1]
                file_decls[file_path].append((short_name, line_num, full_name))

    return dict(file_decls)


def generate_namespace_variants(full_name: str) -> List[str]:
    """
    Generate all namespace variants for a declaration.

    Example:
        Input: "TDCSG.CompoundSymmetry.GG5.E_re"
        Output: ["E_re", "GG5.E_re", "CompoundSymmetry.GG5.E_re",
                 "TDCSG.CompoundSymmetry.GG5.E_re"]
    """
    components = full_name.split('.')
    variants = []

    # Short name (no namespace)
    variants.append(components[-1])

    # Progressive prefixes
    for i in range(len(components) - 2, -1, -1):
        variant = '.'.join(components[i:])
        variants.append(variant)

    return variants


def search_declaration_in_files(
    decl_name: str,
    search_dir: Path,
    definition_file: str,
    definition_line: int
) -> Tuple[int, Set[str]]:
    """
    Search for declaration name in all .lean files.

    Args:
        decl_name: Declaration name (any namespace variant)
        search_dir: Directory to search (typically TDCSG/)
        definition_file: File where declaration is defined
        definition_line: Line number of definition

    Returns:
        (occurrence_count_excluding_definition, set_of_files_found_in)
    """
    # Use word boundaries to match whole identifiers only
    # Escape special characters (like ') that might be in Lean identifiers
    pattern = rf'\b{re.escape(decl_name)}\b'
    regex = re.compile(pattern)

    total_count = 0
    files_found = set()

    # Find all .lean files
    lean_files = sorted(search_dir.rglob('*.lean'))

    for file_path in lean_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()

            for line_num, line in enumerate(lines, start=1):
                matches = regex.findall(line)
                if matches:
                    # Check if this is the definition line (exclude it from count)
                    is_definition = (
                        str(file_path) == definition_file and
                        line_num == definition_line
                    )

                    if not is_definition:
                        total_count += len(matches)
                        files_found.add(file_path.name)

        except Exception as e:
            print(f"⚠️  Warning: Could not read {file_path}: {e}", file=sys.stderr)

    return total_count, files_found


def generate_report(dead_code_path: Path, search_dir: Path, output_path: Path):
    """
    Generate string-based analysis report.

    For each declaration:
    - Search all namespace variants
    - Count occurrences (excluding definition)
    - Determine KEEP/DELETE action
    - Write to report file
    """
    print("=== STRING-BASED DEAD CODE ANALYSIS ===\n")
    print(f"📖 Reading: {dead_code_path}")

    file_decls = parse_dead_code_file(dead_code_path)
    total_decls = sum(len(decls) for decls in file_decls.values())

    print(f"📊 Found {total_decls} user-written declarations to analyze\n")
    print(f"🔍 Searching in: {search_dir}\n")

    # Collect results
    results = []

    for file_path, declarations in sorted(file_decls.items()):
        for short_name, line_num, full_name in declarations:
            # Generate namespace variants
            variants = generate_namespace_variants(full_name)

            # Search for each variant and aggregate results
            max_count = 0
            all_files = set()

            for variant in variants:
                count, files = search_declaration_in_files(
                    variant, search_dir, file_path, line_num
                )
                if count > max_count:
                    max_count = count
                    all_files = files
                elif count == max_count:
                    all_files.update(files)

            # Determine action
            action = "DELETE" if max_count == 0 else "KEEP"

            results.append({
                'action': action,
                'name': short_name,
                'count': max_count,
                'files': sorted(all_files),
                'full_name': full_name,
                'def_file': file_path,
                'def_line': line_num
            })

            # Progress indicator
            status_symbol = "❌" if action == "DELETE" else "✅"
            print(f"{status_symbol} {short_name:30s} count={max_count:3d}  files={len(all_files)}")

    # Write report
    print(f"\n📝 Writing report to: {output_path}")

    with open(output_path, 'w', encoding='utf-8') as f:
        # Header
        f.write("# String-Based Dead Code Analysis\n")
        f.write(f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write("#\n")
        f.write("# Instructions:\n")
        f.write("# - Edit KEEP/DELETE actions as needed\n")
        f.write("# - Lines starting with # are comments (ignored)\n")
        f.write("# - Format: ACTION    name    count=N    files=[...]\n")
        f.write("#\n")
        f.write("# After editing, run: python scripts/string_search_analyzer.py --execute-deletions\n")
        f.write("\n")

        # Results
        for result in results:
            action = result['action']
            name = result['name']
            count = result['count']
            files = result['files']

            # Format files list
            if len(files) <= 3:
                files_str = ', '.join(files)
            else:
                files_str = ', '.join(files[:3]) + f', ... (+{len(files) - 3} more)'

            f.write(f"{action:6s}  {name:30s} count={count:3d}    files=[{files_str}]\n")

    # Summary
    keep_count = sum(1 for r in results if r['action'] == 'KEEP')
    delete_count = sum(1 for r in results if r['action'] == 'DELETE')

    print(f"\n{'='*60}")
    print(f"📊 Analysis complete:")
    print(f"   KEEP:   {keep_count:3d} declarations ({keep_count*100//total_decls:2d}%)")
    print(f"   DELETE: {delete_count:3d} declarations ({delete_count*100//total_decls:2d}%)")
    print(f"\n📋 Next steps:")
    print(f"   1. Review and edit: {output_path}")
    print(f"   2. Run: python scripts/string_search_analyzer.py --execute-deletions --dry-run")
    print(f"   3. Run: python scripts/string_search_analyzer.py --execute-deletions")


def parse_report_file(report_path: Path) -> Dict[str, List[Tuple[str, int]]]:
    """
    Parse the analysis report for DELETE actions.

    Returns: Dict[file_path, List[(decl_name, line_num)]]
    """
    print(f"📖 Reading report: {report_path}\n")

    # First, need to map declaration names back to their file:line locations
    # We'll use the dead_code.txt as the source of truth for locations
    dead_code_path = Path('docs/dead_code.txt')
    all_decls = parse_dead_code_file(dead_code_path)

    # Create lookup: short_name -> (file, line)
    name_to_location = {}
    for file_path, declarations in all_decls.items():
        for short_name, line_num, full_name in declarations:
            name_to_location[short_name] = (file_path, line_num)

    # Parse report for DELETE actions
    deletions = defaultdict(list)

    with open(report_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()

            # Skip comments and empty lines
            if not line or line.startswith('#'):
                continue

            # Parse format: ACTION  name  count=N  files=[...]
            match = re.match(r'^(KEEP|DELETE)\s+(\S+)', line)
            if match:
                action = match.group(1)
                name = match.group(2)

                if action == 'DELETE':
                    # Look up location
                    if name in name_to_location:
                        file_path, line_num = name_to_location[name]
                        deletions[file_path].append((name, line_num))
                    else:
                        print(f"⚠️  Warning: Cannot find location for {name}", file=sys.stderr)

    return dict(deletions)


def find_declaration_block(lines: List[str], start_idx: int) -> Tuple[int, int]:
    """
    Find doc comment + declaration boundaries.

    Reused from simple_delete_dead_code.py (proven safe implementation).

    Returns: (start_line, end_line) inclusive
    """
    # Backward scan for doc comments
    doc_start = start_idx
    i = start_idx - 1

    while i >= 0 and not lines[i].strip():
        i -= 1  # Skip blank lines

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

    # Forward scan for declaration end
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


def clean_blank_lines_list(lines: List[str]) -> List[str]:
    """Clean excessive blank lines (max 2 consecutive)."""
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
    return cleaned


def execute_deletions(report_path: Path, dry_run: bool = False):
    """
    Execute deletions based on report file.

    Reads report, deletes declarations marked DELETE.
    """
    print("=== DELETION EXECUTION ===\n")
    if dry_run:
        print("🔍 DRY RUN MODE - No files will be modified\n")

    # Parse report
    deletions = parse_report_file(report_path)

    if not deletions:
        print("✅ No deletions to perform")
        return

    total_to_delete = sum(len(decls) for decls in deletions.values())
    print(f"📊 Will delete {total_to_delete} declarations from {len(deletions)} files\n")

    # Create backup if not dry run
    if not dry_run:
        backup_dir = Path('backup')
        backup_dir.mkdir(exist_ok=True)

        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup_path = backup_dir / f'pre_string_deletion_{timestamp}.tar.gz'

        print(f"💾 Creating backup: {backup_path}")
        with tarfile.open(backup_path, 'w:gz') as tar:
            for file_path in deletions.keys():
                if Path(file_path).exists():
                    tar.add(file_path, arcname=file_path)
        print(f"   ✅ Backed up {len(deletions)} files\n")

    # Process deletions
    deleted_count = 0
    deleted_names = []

    for file_path in sorted(deletions.keys()):
        decls = deletions[file_path]
        print(f"📄 {file_path} ({len(decls)} declarations)...")

        file_path_obj = Path(file_path)
        if not file_path_obj.exists():
            print(f"   ⚠️  File not found, skipping")
            continue

        with open(file_path_obj, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Sort by line descending - delete bottom-up
        decls_sorted = sorted(decls, key=lambda x: x[1], reverse=True)

        ranges_to_delete = []
        for decl_name, line_num in decls_sorted:
            idx = line_num - 1  # Convert to 0-indexed

            if idx < 0 or idx >= len(lines):
                print(f"   ⚠️  Invalid line number for {decl_name}")
                continue

            if decl_name not in lines[idx]:
                print(f"   ⚠️  Declaration {decl_name} not found at line {line_num}")
                continue

            start, end = find_declaration_block(lines, idx)
            ranges_to_delete.append((start, end, decl_name))
            print(f"   🗑️  {decl_name} (lines {start + 1}-{end + 1})")

        if not ranges_to_delete:
            continue

        if not dry_run:
            # Delete ranges bottom-up
            for start, end, name in ranges_to_delete:
                del lines[start:end + 1]
                deleted_names.append(name)
                deleted_count += 1

            # Clean blank lines
            lines = clean_blank_lines_list(lines)

            # Write back
            with open(file_path_obj, 'w', encoding='utf-8') as f:
                f.writelines(lines)

        else:
            deleted_count += len(ranges_to_delete)

        print()

    # Save deletion report
    if not dry_run and deleted_names:
        report_out = Path('docs/deleted_declarations_string_based.txt')
        with open(report_out, 'w', encoding='utf-8') as f:
            f.write(f"Deleted {deleted_count} declarations at {datetime.now().isoformat()}\n\n")
            for name in sorted(deleted_names):
                f.write(f"{name}\n")
        print(f"📋 Deletion report: {report_out}\n")

    # Summary
    print("=" * 60)
    if dry_run:
        print(f"🔍 Would delete {deleted_count} declarations")
    else:
        print(f"✅ Deleted {deleted_count} declarations")
        if deleted_count > 0:
            print(f"💾 Backup: {backup_path}")
        print(f"\n📋 Next: lake build (verify code still compiles)")


def main():
    parser = argparse.ArgumentParser(description='String-based dead code analyzer')
    parser.add_argument('--generate-report', action='store_true',
                        help='Generate analysis report')
    parser.add_argument('--execute-deletions', action='store_true',
                        help='Execute deletions based on report')
    parser.add_argument('--dry-run', action='store_true',
                        help='Preview deletions without modifying files')
    args = parser.parse_args()

    if not args.generate_report and not args.execute_deletions:
        print("❌ Error: Must specify --generate-report or --execute-deletions")
        parser.print_help()
        sys.exit(1)

    if args.generate_report and args.execute_deletions:
        print("❌ Error: Cannot specify both --generate-report and --execute-deletions")
        sys.exit(1)

    if args.generate_report:
        # Generate report mode
        dead_code_path = Path('docs/dead_code.txt')
        search_dir = Path('TDCSG')
        output_path = Path('docs/dead_code_string_analysis.txt')

        if not dead_code_path.exists():
            print(f"❌ Error: {dead_code_path} not found")
            sys.exit(1)

        if not search_dir.exists():
            print(f"❌ Error: {search_dir} directory not found")
            sys.exit(1)

        generate_report(dead_code_path, search_dir, output_path)

    elif args.execute_deletions:
        # Deletion execution mode
        report_path = Path('docs/dead_code_string_analysis.txt')

        if not report_path.exists():
            print(f"❌ Error: {report_path} not found")
            print("   Run --generate-report first")
            sys.exit(1)

        execute_deletions(report_path, args.dry_run)


if __name__ == "__main__":
    main()
