#!/usr/bin/env bash
# Deploy documentation to GitHub Pages
# Usage: ./scripts/deploy_docs.sh [commit message]

set -e  # Exit on error

COMMIT_MSG="${1:-Update documentation}"

echo "🚀 Deploying documentation to GitHub Pages..."

# Ensure we're in project root
cd "$(dirname "$0")/.."

# Check if docs exist
if [ ! -d ".lake/build/doc" ]; then
    echo "❌ Documentation not found. Run ./scripts/build_docs.sh first!"
    exit 1
fi

# Check if we have uncommitted changes
if ! git diff-index --quiet HEAD --; then
    echo "⚠️  You have uncommitted changes in your working directory."
    echo "   Please commit or stash them first."
    exit 1
fi

# Save current branch
CURRENT_BRANCH=$(git branch --show-current)

# Create or switch to gh-pages branch
if git show-ref --verify --quiet refs/heads/gh-pages; then
    echo "📋 Switching to existing gh-pages branch..."
    git checkout gh-pages
else
    echo "🌱 Creating new gh-pages branch..."
    git checkout --orphan gh-pages
    git rm -rf .
fi

# Copy documentation
echo "📂 Copying documentation..."
cp -r .lake/build/doc/* .

# Add landing page if it doesn't exist
if [ ! -f "index.html" ] && [ -f "landing/index.html" ]; then
    cp landing/index.html index.html
fi

# Create .nojekyll to prevent GitHub from processing with Jekyll
touch .nojekyll

# Commit and push
echo "💾 Committing changes..."
git add -A
git commit -m "$COMMIT_MSG" || {
    echo "ℹ️  No changes to commit"
    git checkout "$CURRENT_BRANCH"
    exit 0
}

echo "📤 Pushing to GitHub..."
git push origin gh-pages

# Return to original branch
echo "🔙 Returning to $CURRENT_BRANCH..."
git checkout "$CURRENT_BRANCH"

echo "✅ Documentation deployed successfully!"
echo "🌐 Visit: https://$(git config --get remote.origin.url | sed 's/.*github.com[:/]\([^/]*\)\/\([^.]*\).*/\1.github.io\/\2/')/"
