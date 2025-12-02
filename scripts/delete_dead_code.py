#!/usr/bin/env python3
"""
Delete dead code declarations from Lean source files.

Reads docs/dead_code.txt and removes all unreachable declarations from source files.
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict


def parse_dead_code_file(dead_code_path: Path) -> Dict[str, List[Tuple[str, int]]]:
    """
    Parse docs/dead_code.txt to extract file:line mappings.

    Returns: Dict[file_path, List[(decl_name, line_number)]]
    """
    file_decls = defaultdict(list)

    with open(dead_code_path) as f:
        for line in f:
            line = line.strip()
            # Look for pattern: NAME (kind) (file:line)
            match = re.search(r'^(\S+)\s+\((\w+)\)\s+\(([^:]+):(\d+)\)', line)
            if match:
                full_name = match.group(1)
                kind = match.group(2)
                file_path = match.group(3)
                line_num = int(match.group(4))

                # Extract just the declaration name (last component)
                decl_name = full_name.split('.')[-1]
                file_decls[file_path].append((decl_name, line_num))

    return dict(file_decls)


def find_declaration_end(lines: List[str], start_idx: int, decl_name: str) -> int:
    """
    Find where a declaration ends by looking for the next top-level declaration
    or end of file.

    Returns: Index of last line belonging to this declaration (inclusive)
    """
    # Get the indentation level of the declaration
    start_line = lines[start_idx]
    start_indent = len(start_line) - len(start_line.lstrip())

    # Keywords that mark top-level declarations at same or lower indentation
    decl_keywords = ['def ', 'theorem ', 'lemma ', 'axiom ', 'inductive ',
                     'structure ', 'class ', 'instance ', 'abbrev ', 'opaque ']

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


def remove_declarations_from_file(file_path: str, declarations: List[Tuple[str, int]]) -> bool:
    """
    Remove specified declarations from a Lean file.

    Args:
        file_path: Path to Lean source file
        declarations: List of (decl_name, line_number) tuples

    Returns: True if file was modified, False otherwise
    """
    path = Path(file_path)
    if not path.exists():
        print(f"  ⚠️  File not found: {file_path}")
        return False

    # Read file
    with open(path) as f:
        lines = f.readlines()

    # Sort declarations by line number (descending) to delete from bottom up
    declarations_sorted = sorted(declarations, key=lambda x: x[1], reverse=True)

    # Track which lines to delete
    lines_to_delete: Set[int] = set()

    for decl_name, line_num in declarations_sorted:
        # Convert to 0-indexed
        idx = line_num - 1

        if idx < 0 or idx >= len(lines):
            print(f"  ⚠️  Invalid line number {line_num} for {decl_name}")
            continue

        # Verify this line contains the declaration
        line = lines[idx]
        if decl_name not in line:
            print(f"  ⚠️  Declaration {decl_name} not found at line {line_num}")
            continue

        # Check for doc comment immediately before declaration
        start_idx = idx
        i = idx - 1
        while i >= 0 and (not lines[i].strip() or lines[i].strip().startswith('--')):
            if lines[i].strip().startswith('/-'):
                # Found start of multiline doc comment
                start_idx = i
                break
            elif lines[i].strip().startswith('--'):
                # Single line doc comment
                start_idx = i
            i -= 1

        # Find the end of this declaration
        end_idx = find_declaration_end(lines, idx, decl_name)

        # Mark all lines in this range for deletion (including doc comment if present)
        for i in range(start_idx, end_idx + 1):
            lines_to_delete.add(i)

        if start_idx < idx:
            print(f"  🗑️  Removing {decl_name} with doc comment (lines {start_idx + 1}-{end_idx + 1})")
        else:
            print(f"  🗑️  Removing {decl_name} (lines {line_num}-{end_idx + 1})")

    if not lines_to_delete:
        print(f"  ℹ️  No declarations removed from {file_path}")
        return False

    # Create new content with deleted lines removed
    new_lines = [line for i, line in enumerate(lines) if i not in lines_to_delete]

    # Remove excessive blank lines (more than 2 consecutive)
    cleaned_lines = []
    blank_count = 0
    for line in new_lines:
        if line.strip():
            cleaned_lines.append(line)
            blank_count = 0
        else:
            blank_count += 1
            if blank_count <= 2:
                cleaned_lines.append(line)

    # Write back
    with open(path, 'w') as f:
        f.writelines(cleaned_lines)

    removed_count = len(lines_to_delete)
    print(f"  ✅ Removed {removed_count} lines from {file_path}")
    return True


def main():
    # Parse dead code file
    dead_code_path = Path("docs/dead_code.txt")
    if not dead_code_path.exists():
        print("❌ Error: docs/dead_code.txt not found")
        print("Run 'lake exe find_dead_code' first")
        sys.exit(1)

    print("=== DEAD CODE DELETION ===\n")
    print("📖 Reading dead code analysis...")

    file_decls = parse_dead_code_file(dead_code_path)

    if not file_decls:
        print("✅ No dead code with file locations found")
        sys.exit(0)

    total_files = len(file_decls)
    total_decls = sum(len(decls) for decls in file_decls.values())

    print(f"📊 Found {total_decls} declarations across {total_files} files\n")

    # Process each file
    modified_files = 0
    for file_path in sorted(file_decls.keys()):
        decls = file_decls[file_path]
        print(f"📄 Processing {file_path} ({len(decls)} declarations)...")

        if remove_declarations_from_file(file_path, decls):
            modified_files += 1
        print()

    print("=" * 60)
    print(f"✅ COMPLETE: Modified {modified_files}/{total_files} files")
    print("\n📋 Next steps:")
    print("  1. Run: lake build")
    print("  2. Run: lake env lean --run KMVerify/Main.lean")
    print("  3. Run: lake exe find_dead_code  (should show 0 dead code)")
    print("  4. If build fails: git restore .")


if __name__ == "__main__":
    main()
