#!/bin/bash
set -e

# Get script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_ROOT"

echo "=== Dead Code Analysis Workflow ==="
echo ""

# Step 1: Run the Lean dead code analyzer
echo "Step 1/2: Running Lean dead code analyzer..."
echo "  (This may take a minute...)"
lake exe find_dead_code 2>&1 | grep -v "warning:" | tail -20
echo ""

# Step 2: Run the Python simp attribute checker
echo "Step 2/2: Checking for @[simp] attributes..."
python3 scripts/check_simp_attrs.py
echo ""

echo "=== Analysis Complete ==="
echo ""
echo "Generated reports:"
echo "  📄 docs/dead_code_analysis.md    - Human-readable report with safety warnings"
echo "  📄 docs/dead_code.txt            - Simple list format"
echo "  ⚠️  docs/dead_code_safety.txt     - @[simp] declarations that MUST NOT be deleted"
echo ""
echo "Next steps:"
echo "  1. Review docs/dead_code_safety.txt for dangerous declarations"
echo "  2. Review docs/dead_code_analysis.md for potentially safe deletions"
echo "  3. After deletions: lake build && lake env lean --run KMVerify/Main.lean"
