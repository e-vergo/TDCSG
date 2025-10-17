#!/usr/bin/env python3
"""
Check multiple Lean files and provide aggregated summary.
Usage: python3 check_lean_multi.py <mode> <file1> <file2> ...
where mode is: errors-only, warnings, sorries, or warnings-summary
"""

import sys
import subprocess
import os
from pathlib import Path
from typing import List, Tuple, Dict

def check_file(file_path: str, mode: str, script_dir: str) -> Tuple[str, int, str]:
    """
    Check a single file using the appropriate mode.

    Args:
        file_path: Path to Lean file
        mode: One of 'errors-only', 'warnings', 'sorries', 'warnings-summary'
        script_dir: Directory containing check scripts

    Returns:
        Tuple of (file_path, exit_code, output)
    """
    # Map mode to Python script
    script_map = {
        'errors-only': 'check_lean_errors_only.py',
        'warnings': 'check_lean_file.py',
        'sorries': 'check_lean_sorries.py',
        'warnings-summary': 'check_lean_warnings_summary.py',
    }

    script_name = script_map.get(mode)
    if not script_name:
        return (file_path, 2, f"Error: Unknown mode '{mode}'")

    script_path = os.path.join(script_dir, script_name)

    try:
        # Run lake build and pipe to Python script
        build_proc = subprocess.Popen(
            ['lake', 'build', file_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True
        )

        filter_proc = subprocess.Popen(
            ['python3', script_path, file_path],
            stdin=build_proc.stdout,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True
        )

        build_proc.stdout.close()
        output, _ = filter_proc.communicate()
        exit_code = filter_proc.returncode

        return (file_path, exit_code, output.strip())

    except Exception as e:
        return (file_path, 2, f"Error checking {file_path}: {str(e)}")


def format_multi_file_summary(results: List[Tuple[str, int, str]], mode: str) -> str:
    """
    Format results from multiple files into a summary.

    Args:
        results: List of (file_path, exit_code, output) tuples
        mode: The mode used for checking

    Returns:
        Formatted string
    """
    output = []

    # Summary header
    output.append("Build Status Summary:")

    clean_files = []
    failed_files = []

    for file_path, exit_code, file_output in results:
        if exit_code == 0:
            clean_files.append(file_path)
            output.append(f"  ✓ {file_path}: Clean")
        else:
            failed_files.append((file_path, file_output))
            # Extract count from output if possible
            if mode == 'errors-only':
                output.append(f"  ✗ {file_path}: Has errors")
            elif mode in ['warnings', 'warnings-summary']:
                # Try to extract warning count
                count_match = None
                for line in file_output.split('\n'):
                    if 'Total:' in line and 'warning' in line:
                        count_match = line
                        break
                if count_match:
                    output.append(f"  ✗ {file_path}: {count_match.split('Total:')[1].strip()}")
                else:
                    output.append(f"  ✗ {file_path}: Has warnings")
            elif mode == 'sorries':
                # Extract sorry count
                count_match = None
                for line in file_output.split('\n'):
                    if 'Total:' in line and 'sorries' in line:
                        count_match = line
                        break
                if count_match:
                    output.append(f"  ✗ {file_path}: {count_match.split('Total:')[1].strip()}")
                else:
                    output.append(f"  ✗ {file_path}: Has sorries")

    output.append("")

    # Overall result
    total = len(results)
    clean_count = len(clean_files)

    if mode == 'errors-only':
        if failed_files:
            output.append(f"Result: {clean_count}/{total} files compile without errors ✗\n")
        else:
            output.append(f"Result: {total}/{total} files compile without errors ✓\n")
    elif mode in ['warnings', 'warnings-summary']:
        if failed_files:
            output.append(f"Result: {clean_count}/{total} files have no warnings ✗\n")
        else:
            output.append(f"Result: {total}/{total} files are warning-free ✓\n")
    elif mode == 'sorries':
        if failed_files:
            output.append(f"Result: {clean_count}/{total} files have no sorries ✗\n")
        else:
            output.append(f"Result: {total}/{total} files are sorry-free ✓\n")

    # Show details for failed files
    if failed_files:
        output.append("Showing details for files with issues:\n")
        for file_path, file_output in failed_files:
            output.append(f"=== {file_path} ===")
            output.append(file_output)
            output.append("")

    return '\n'.join(output)


def main():
    if len(sys.argv) < 3:
        print("Usage: python3 check_lean_multi.py <mode> <file1> [file2] ...", file=sys.stderr)
        print("", file=sys.stderr)
        print("Modes:", file=sys.stderr)
        print("  errors-only      - Show only errors", file=sys.stderr)
        print("  warnings         - Show all warnings", file=sys.stderr)
        print("  sorries          - Show sorry summary", file=sys.stderr)
        print("  warnings-summary - Show warning summary", file=sys.stderr)
        print("", file=sys.stderr)
        print("Example:", file=sys.stderr)
        print("  python3 check_lean_multi.py errors-only TDCSG/*.lean", file=sys.stderr)
        sys.exit(1)

    mode = sys.argv[1]
    file_paths = sys.argv[2:]

    # Get script directory
    script_dir = os.path.dirname(os.path.abspath(__file__))

    # Check all files
    results = []
    for file_path in file_paths:
        result = check_file(file_path, mode, script_dir)
        results.append(result)

    # Format and print summary
    output = format_multi_file_summary(results, mode)
    print(output)

    # Exit with error code if any file failed
    any_failed = any(exit_code != 0 for _, exit_code, _ in results)
    sys.exit(1 if any_failed else 0)


if __name__ == '__main__':
    main()
