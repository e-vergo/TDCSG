#!/usr/bin/env python3
"""
Check which declarations in dead_code.txt actually have @[simp] or other attributes.
This helps identify which "dead code" declarations are UNSAFE to delete.
"""

import re
from pathlib import Path
from typing import Dict, Set, Tuple

def find_declaration_with_attrs(file_path: Path, decl_name: str, line_num: int) -> Tuple[bool, Set[str]]:
    """
    Check if a declaration has attributes like @[simp].

    Args:
        file_path: Path to the Lean file
        decl_name: Short name of the declaration
        line_num: Line number (1-indexed) where declaration is found

    Returns: (found, attributes_set)
    """
    try:
        content = file_path.read_text()
        lines = content.split('\n')

        # Convert to 0-indexed
        target_line = line_num - 1

        if target_line < 0 or target_line >= len(lines):
            return (False, set())

        # Check if the target line actually contains this declaration
        line = lines[target_line]

        # Must have the decl_name and a keyword
        keywords = ['def ', 'theorem ', 'lemma ', 'instance ', 'abbrev ', 'opaque ']
        has_keyword = any(kw in line for kw in keywords)
        has_name = decl_name in line

        if not (has_keyword and has_name):
            return (False, set())

        # Check previous 5 lines AND the declaration line itself for attributes
        attrs = set()
        for j in range(max(0, target_line - 5), target_line + 1):
            attr_line = lines[j].strip()
            # Match @[...] patterns
            attr_matches = re.findall(r'@\[([^\]]+)\]', attr_line)
            for match in attr_matches:
                # Split by comma to handle @[simp, ext] style
                for attr in match.split(','):
                    attrs.add(attr.strip())

        return (True, attrs)

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return (False, set())

def main():
    project_root = Path(__file__).parent.parent
    dead_code_file = project_root / "docs" / "dead_code.txt"

    if not dead_code_file.exists():
        print(f"Error: {dead_code_file} not found. Run 'lake exe find_dead_code' first.")
        return

    # Parse dead code file
    declarations = []
    with open(dead_code_file) as f:
        for line in f:
            if '(' in line and ')' in line:
                # Extract name and file location
                # Format: TDCSG.CompoundSymmetry.GG5.zeta5_pow_zero (theorem) (TDCSG/Proofs/Zeta5.lean:58)
                match = re.match(r'([\w.]+)\s+\((\w+)\)\s+\(([^:]+):(\d+)\)', line)
                if match:
                    full_name, kind, file_path, line_num = match.groups()
                    short_name = full_name.split('.')[-1]
                    declarations.append({
                        'full_name': full_name,
                        'short_name': short_name,
                        'kind': kind,
                        'file': file_path,
                        'line': int(line_num)
                    })

    print(f"Found {len(declarations)} declarations to check")
    print()

    # Check each declaration for attributes
    simp_decls = []
    other_attrs = []
    no_attrs = []

    for decl in declarations:
        file_path = project_root / decl['file']
        if file_path.exists():
            found, attrs = find_declaration_with_attrs(file_path, decl['short_name'], decl['line'])
            if found and attrs:
                if 'simp' in attrs:
                    simp_decls.append((decl, attrs))
                else:
                    other_attrs.append((decl, attrs))
            else:
                no_attrs.append(decl)

    # Print results
    print("=" * 80)
    print(f"DANGEROUS: {len(simp_decls)} declarations with @[simp] (MUST NOT DELETE)")
    print("=" * 80)
    print()
    for decl, attrs in sorted(simp_decls, key=lambda x: (x[0]['file'], x[0]['line'])):
        attrs_str = ', '.join(f"@[{a}]" for a in sorted(attrs))
        print(f"{decl['file']}:{decl['line']}")
        print(f"  {decl['full_name']} ({decl['kind']})")
        print(f"  Attributes: {attrs_str}")
        print()

    if other_attrs:
        print("=" * 80)
        print(f"CAUTION: {len(other_attrs)} declarations with other attributes")
        print("=" * 80)
        print()
        for decl, attrs in sorted(other_attrs, key=lambda x: (x[0]['file'], x[0]['line'])):
            attrs_str = ', '.join(f"@[{a}]" for a in sorted(attrs))
            print(f"{decl['file']}:{decl['line']}")
            print(f"  {decl['full_name']} ({decl['kind']})")
            print(f"  Attributes: {attrs_str}")
            print()

    print("=" * 80)
    print(f"POTENTIALLY SAFE: {len(no_attrs)} declarations without detected attributes")
    print("=" * 80)
    print()
    print("These declarations may be safe to delete, but still verify manually:")
    by_file = {}
    for decl in no_attrs:
        by_file.setdefault(decl['file'], []).append(decl)

    for file_path in sorted(by_file.keys()):
        decls = sorted(by_file[file_path], key=lambda x: x['line'])
        print(f"\n{file_path} ({len(decls)} declarations):")
        for decl in decls:
            print(f"  Line {decl['line']}: {decl['short_name']} ({decl['kind']})")

    # Save summary
    summary_file = project_root / "docs" / "dead_code_safety.txt"
    with open(summary_file, 'w') as f:
        f.write(f"DANGEROUS (@[simp]): {len(simp_decls)}\n")
        f.write(f"CAUTION (other attrs): {len(other_attrs)}\n")
        f.write(f"POTENTIALLY SAFE: {len(no_attrs)}\n")
        f.write(f"\nDO NOT DELETE these {len(simp_decls)} @[simp] declarations:\n")
        for decl, _ in sorted(simp_decls, key=lambda x: x[0]['full_name']):
            f.write(f"  {decl['full_name']}\n")

    print(f"\n\nSummary saved to: {summary_file}")

if __name__ == "__main__":
    main()
