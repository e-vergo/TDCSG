#!/usr/bin/env bash
# Deploy landing page and blueprint to GitHub Pages (without API docs)
# Usage: ./scripts/deploy_blueprint.sh [commit message]

set -e

COMMIT_MSG="${1:-Update blueprint and landing page}"

echo "🚀 Deploying blueprint to GitHub Pages..."

cd "$(dirname "$0")/.."

# Regenerate dependency graph
echo "📊 Regenerating dependency graph..."
python3 scripts/generate_dep_graph.py

# Check if we have uncommitted changes
if ! git diff-index --quiet HEAD --; then
    echo "⚠️  You have uncommitted changes. Consider committing them first."
    echo "   Continuing anyway..."
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
    git rm -rf . 2>/dev/null || true
fi

# Copy landing page as index.html
echo "📂 Copying landing page..."
cp landing/index.html index.html

# Copy blueprint
echo "📖 Copying blueprint..."
mkdir -p blueprint/web
cp -r blueprint/src/web/* blueprint/web/ 2>/dev/null || true
cp blueprint/web.tex blueprint/ 2>/dev/null || true
cp blueprint/src/content.tex blueprint/ 2>/dev/null || true

# Create placeholder for docs
echo "📚 Creating docs placeholder..."
mkdir -p docs
cat > docs/index.html << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <title>TDCSG Documentation - Building...</title>
    <style>
        body {
            font-family: system-ui, sans-serif;
            display: flex;
            align-items: center;
            justify-content: center;
            min-height: 100vh;
            margin: 0;
            background: #f8fafc;
        }
        .container {
            text-align: center;
            padding: 2rem;
        }
        h1 {
            color: #1e293b;
            margin-bottom: 1rem;
        }
        p {
            color: #64748b;
            margin-bottom: 1.5rem;
        }
        a {
            color: #2563eb;
            text-decoration: none;
            font-weight: 600;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>API Documentation Building...</h1>
        <p>The API documentation is being generated.</p>
        <p>In the meantime, check out:</p>
        <p><a href="../">← Back to Project</a> | <a href="../blueprint/web/dep_graph.html">Dependency Graph</a></p>
    </div>
</body>
</html>
EOF

# Create .nojekyll
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
git push origin gh-pages -f

# Return to original branch
echo "🔙 Returning to $CURRENT_BRANCH..."
git checkout "$CURRENT_BRANCH"

echo "✅ Blueprint deployed successfully!"
echo "🌐 Site will be live shortly at GitHub Pages"
