#!/usr/bin/env python3
"""
Strip all comments from Lean 4 files.

Removes:
- Block comments: /- ... -/
- Doc comments: /-- ... -/ and /-! ... -/
- Line comments: -- ...

Usage:
    python scripts/strip_comments.py TDCSG/ [--dry-run]
    python scripts/strip_comments.py test_data/sample_with_comments.lean [--dry-run]
"""

import argparse
import re
import sys
import tarfile
from datetime import datetime
from pathlib import Path
from typing import List


def strip_comments_from_content(content: str) -> str:
    """
    Remove all comments from Lean code content.

    Uses line-by-line processing to handle:
    - Block comments: /- ... -/ (can span multiple lines)
    - Line comments: -- ... (until end of line)
    - Inline comments after code

    Returns: Comment-free content
    """
    lines = content.split('\n')
    result_lines = []
    in_block_comment = False

    for line in lines:
        result = []
        i = 0

        while i < len(line):
            char = line[i]

            if in_block_comment:
                # Look for end of block comment
                if char == '-' and i + 1 < len(line) and line[i + 1] == '/':
                    in_block_comment = False
                    i += 2  # Skip '-/'
                    continue
                i += 1
                continue

            # Not in block comment - check for comment starts
            if char == '/' and i + 1 < len(line) and line[i + 1] == '-':
                # Start of block comment
                in_block_comment = True
                i += 2
                continue

            if char == '-' and i + 1 < len(line) and line[i + 1] == '-':
                # Line comment - rest of line is comment
                break

            # Regular code character
            result.append(char)
            i += 1

        # Add this line if it has content (after stripping trailing whitespace)
        line_content = ''.join(result).rstrip()
        # Always add the line (even if empty) to preserve structure
        # The clean_blank_lines function will handle excessive blanks
        result_lines.append(line_content)

    return '\n'.join(result_lines)


def clean_blank_lines(content: str) -> str:
    """
    Clean up whitespace:
    - Remove trailing whitespace from lines
    - Reduce consecutive blank lines to max 1
    - Remove leading/trailing blank lines
    - Ensure final newline

    Returns: Content with cleaned blank lines
    """
    lines = content.split('\n')

    # Strip trailing whitespace from each line
    lines = [line.rstrip() for line in lines]

    # Remove leading blank lines
    while lines and not lines[0]:
        lines.pop(0)

    # Remove trailing blank lines
    while lines and not lines[-1]:
        lines.pop()

    # Reduce consecutive blank lines to max 1
    cleaned = []
    blank_count = 0

    for line in lines:
        if line:  # Non-blank line
            cleaned.append(line)
            blank_count = 0
        else:  # Blank line
            blank_count += 1
            if blank_count <= 1:  # Allow only 1 consecutive blank line
                cleaned.append(line)

    # Ensure final newline
    result = '\n'.join(cleaned)
    if result and not result.endswith('\n'):
        result += '\n'

    return result


def strip_file(file_path: Path, dry_run: bool = False) -> bool:
    """
    Strip comments from a single Lean file.

    Returns: True if file was modified (or would be modified in dry-run)
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            original_content = f.read()

        # Strip comments
        stripped_content = strip_comments_from_content(original_content)

        # Clean excessive blank lines
        cleaned_content = clean_blank_lines(stripped_content)

        # Check if anything changed
        if original_content == cleaned_content:
            return False

        if not dry_run:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(cleaned_content)

        return True

    except Exception as e:
        print(f"❌ Error processing {file_path}: {e}", file=sys.stderr)
        return False


def find_lean_files(path: Path) -> List[Path]:
    """Find all .lean files recursively in directory, or return single file."""
    if path.is_file():
        if path.suffix == '.lean':
            return [path]
        else:
            print(f"❌ Error: {path} is not a .lean file", file=sys.stderr)
            return []

    if path.is_dir():
        return sorted(path.rglob('*.lean'))

    print(f"❌ Error: {path} does not exist", file=sys.stderr)
    return []


def create_backup(files: List[Path], backup_dir: Path) -> Path:
    """
    Create compressed backup of files before modification.

    Returns: Path to backup tarball
    """
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    backup_path = backup_dir / f'pre_comment_strip_{timestamp}.tar.gz'

    print(f"💾 Creating backup: {backup_path}")

    with tarfile.open(backup_path, 'w:gz') as tar:
        for file_path in files:
            if file_path.exists():
                tar.add(file_path, arcname=str(file_path))

    print(f"   ✅ Backed up {len(files)} files")
    return backup_path


def main():
    parser = argparse.ArgumentParser(description='Strip all comments from Lean 4 files')
    parser.add_argument('path', type=Path, help='File or directory to process')
    parser.add_argument('--dry-run', action='store_true', help='Preview changes without modifying files')
    args = parser.parse_args()

    if not args.path.exists():
        print(f"❌ Error: {args.path} does not exist", file=sys.stderr)
        sys.exit(1)

    print("=== LEAN COMMENT STRIPPER ===\n")
    if args.dry_run:
        print("🔍 DRY RUN MODE - No files will be modified\n")

    # Find all Lean files
    lean_files = find_lean_files(args.path)
    if not lean_files:
        print("❌ No .lean files found")
        sys.exit(1)

    print(f"📊 Found {len(lean_files)} .lean file(s)\n")

    # Create backup if not dry run
    if not args.dry_run:
        backup_dir = Path('backup')
        backup_dir.mkdir(exist_ok=True)
        backup_path = create_backup(lean_files, backup_dir)
        print()

    # Process files
    modified_count = 0
    for file_path in lean_files:
        was_modified = strip_file(file_path, args.dry_run)
        if was_modified:
            modified_count += 1
            status = "Would modify" if args.dry_run else "Modified"
            print(f"✏️  {status}: {file_path}")

    # Summary
    print("\n" + "=" * 60)
    if args.dry_run:
        print(f"🔍 Would modify {modified_count} of {len(lean_files)} files")
    else:
        print(f"✅ Modified {modified_count} of {len(lean_files)} files")
        if modified_count > 0:
            print(f"💾 Backup saved to: {backup_path}")

    print("\n📋 Next steps:")
    if args.dry_run:
        print("   Run without --dry-run to apply changes")
    else:
        print("   Run 'lake build' to verify code still compiles")


if __name__ == "__main__":
    main()
