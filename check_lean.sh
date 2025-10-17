#!/usr/bin/env bash
#
# check_lean.sh - Build and extract diagnostics for a specific Lean file
#
# Usage:
#   ./check_lean.sh <filename>              # Show errors AND warnings
#   ./check_lean.sh --errors-only <filename> # Show ONLY errors (no warnings)
#
# Examples:
#   ./check_lean.sh TDCSG/Examples.lean
#   ./check_lean.sh --errors-only TDCSG/Composition.lean
#
# Returns:
#   - Exit code 0 if no issues found
#   - Exit code 1 if errors/warnings exist
#   - Exit code 2 for usage errors
#
# This script ensures agents always see ALL relevant diagnostics with full
# context, never clipped by head/tail commands.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Parse arguments
ERRORS_ONLY=false
LEAN_FILE=""

if [ $# -eq 1 ]; then
    LEAN_FILE="$1"
elif [ $# -eq 2 ] && [ "$1" = "--errors-only" ]; then
    ERRORS_ONLY=true
    LEAN_FILE="$2"
else
    echo "Usage: $0 [--errors-only] <filename>" >&2
    echo "" >&2
    echo "Examples:" >&2
    echo "  $0 TDCSG/Examples.lean              # Show all diagnostics" >&2
    echo "  $0 --errors-only TDCSG/Examples.lean # Show only errors" >&2
    exit 2
fi

# Select appropriate Python script
if [ "$ERRORS_ONLY" = true ]; then
    PYTHON_SCRIPT="$SCRIPT_DIR/check_lean_errors_only.py"
else
    PYTHON_SCRIPT="$SCRIPT_DIR/check_lean_file.py"
fi

# Verify Python script exists
if [ ! -f "$PYTHON_SCRIPT" ]; then
    echo "Error: Python script not found at $PYTHON_SCRIPT" >&2
    exit 2
fi

# Build the file and pipe through Python filter
if output=$(lake build "$LEAN_FILE" 2>&1 | python3 "$PYTHON_SCRIPT" "$LEAN_FILE" 2>&1); then
    # Success case
    echo "$output"
    exit 0
else
    # Failure case (has diagnostics)
    echo "$output"
    exit 1
fi
