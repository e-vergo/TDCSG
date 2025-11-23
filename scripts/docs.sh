#!/usr/bin/env bash
# One-liner to build and deploy docs
# Usage: ./scripts/docs.sh [commit message]

set -e

echo "📚 Building and deploying documentation..."
./scripts/build_docs.sh && ./scripts/deploy_docs.sh "${1:-Update documentation}"
