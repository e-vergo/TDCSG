#!/usr/bin/env bash
# Build documentation locally
# Usage: ./scripts/build_docs.sh

set -e  # Exit on error

echo "🔧 Building TDCSG documentation..."

# Ensure we're in project root
cd "$(dirname "$0")/.."

# Update doc-gen4 dependency
echo "📦 Updating doc-gen4..."
lake -R -Kenv=dev update doc-gen4

# Build the project first
echo "🏗️  Building Lean project..."
lake build

# Generate documentation
echo "📚 Generating documentation..."
lake -R -Kenv=dev build TDCSG:docs

echo "✅ Documentation built successfully!"
echo "📁 Output: .lake/build/doc/"
echo ""
echo "To view locally:"
echo "  cd .lake/build/doc && python3 -m http.server 8000"
echo "  Then visit: http://localhost:8000"
