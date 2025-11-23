# Documentation Deployment Guide

Fast iteration workflow for building and deploying documentation to GitHub Pages.

## Quick Start

### 1. First-Time Setup

```bash
# Get doc-gen4 dependency
lake -R -Kenv=dev update doc-gen4
```

### 2. Build Documentation Locally (~2-5 minutes)

```bash
./scripts/build_docs.sh
```

This builds the entire documentation in `.lake/build/doc/`.

### 3. Preview Locally

```bash
cd .lake/build/doc
python3 -m http.server 8000
# Visit http://localhost:8000
```

### 4. Deploy to GitHub Pages (~30 seconds)

```bash
./scripts/deploy_docs.sh "Update docs"
```

This pushes to the `gh-pages` branch. Your site will be live at:
`https://eric.github.io/TDCSG/`

## Workflow Details

### Build Process

The build script:
1. Updates doc-gen4 dependency
2. Builds your Lean project (`lake build`)
3. Generates HTML documentation (`lake -R -Kenv=dev build TDCSG:docs`)

**Output:** `.lake/build/doc/` directory with:
- `index.html` - Landing page with project structure
- Module documentation pages
- Search functionality
- Source code links

### Deployment Process

The deploy script:
1. Checks that docs exist
2. Ensures working directory is clean
3. Switches to `gh-pages` branch (creates if needed)
4. Copies `.lake/build/doc/*` to branch root
5. Adds landing page from `landing/index.html`
6. Creates `.nojekyll` file
7. Commits and pushes
8. Returns to your original branch

**Result:** Clean deployment without polluting your main branch.

## Time Estimates

| Step | First Time | Subsequent |
|------|------------|------------|
| Update doc-gen4 | ~2 min | ~5 sec |
| Build project | ~3 min | ~30 sec* |
| Generate docs | ~2 min | ~1 min |
| Deploy to GitHub | ~30 sec | ~30 sec |
| **Total** | **~7-8 min** | **~2-3 min** |

*Assumes no Lean file changes; Lake caches aggressively

## Fast Iteration Tips

### 1. Build Only When Needed

Documentation only needs rebuilding when:
- You change `.lean` files
- You add new modules
- You update doc-strings

**Don't rebuild** for:
- README changes
- Landing page updates
- Non-code changes

### 2. Incremental Workflow

```bash
# Edit Lean files
vim TDCSG/CompoundSymmetry/GG5/Geometry.lean

# Build just your project (fast)
lake build

# Generate docs
lake -R -Kenv=dev build TDCSG:docs

# Preview
cd .lake/build/doc && python3 -m http.server 8000

# Deploy when happy
./scripts/deploy_docs.sh
```

### 3. Batch Changes

Make multiple edits, then build once:
```bash
# Edit several files...
# Then:
./scripts/build_docs.sh
./scripts/deploy_docs.sh "Add theorems X, Y, Z"
```

### 4. Landing Page Iterations

To update just the landing page:

```bash
# Edit landing/index.html
vim landing/index.html

# Quick deploy (skips doc rebuild)
git checkout gh-pages
cp landing/index.html .
git add index.html
git commit -m "Update landing page"
git push origin gh-pages
git checkout main
```

## GitHub Pages Setup

### Enable GitHub Pages

1. Go to repository Settings > Pages
2. Source: Deploy from branch
3. Branch: `gh-pages` / `(root)`
4. Save

Your site will be live in ~1 minute at:
`https://eric.github.io/TDCSG/`

### Custom Domain (Optional)

Add a `CNAME` file to `landing/`:
```bash
echo "docs.yourdomain.com" > landing/CNAME
./scripts/deploy_docs.sh
```

Then configure DNS with GitHub's IPs.

## CI/CD (Optional)

If you want automated deployments on git tags:

```yaml
# .github/workflows/docs.yml
name: Deploy Docs
on:
  push:
    tags:
      - 'v*'
  workflow_dispatch:

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: leanprover/lean4-action@v1
      - name: Build docs
        run: ./scripts/build_docs.sh
      - name: Deploy
        run: ./scripts/deploy_docs.sh "Release ${{ github.ref_name }}"
```

This only runs on version tags, keeping CI fast.

## Troubleshooting

### "Documentation not found"

```bash
# Build docs first
./scripts/build_docs.sh
```

### "Uncommitted changes"

```bash
# Commit or stash your work
git add .
git commit -m "WIP"
# Or:
git stash
```

### Build fails

```bash
# Clean build
lake clean
lake build
lake -R -Kenv=dev build TDCSG:docs
```

### Wrong GitHub URL

Edit `scripts/deploy_docs.sh` line 53 to hardcode your URL.

## Comparison: Local vs CI

| Method | First Build | Updates | Pros | Cons |
|--------|-------------|---------|------|------|
| **Local** | ~7-8 min | ~2-3 min | Fast iteration, full control | Manual step |
| **GitHub Actions** | ~25-30 min | ~25-30 min | Automated | Very slow, costs Actions minutes |

**Recommendation:** Local builds for development, optional CI for releases.

## File Structure

```
TDCSG/
├── scripts/
│   ├── build_docs.sh      # Build documentation locally
│   └── deploy_docs.sh     # Deploy to gh-pages
├── landing/
│   └── index.html         # Project landing page
├── .lake/build/doc/       # Generated documentation (gitignored)
└── lakefile.lean          # Includes doc-gen4 dependency
```

## Next Steps

1. **Try it out:**
   ```bash
   ./scripts/build_docs.sh
   ./scripts/deploy_docs.sh
   ```

2. **Customize landing page:**
   Edit `landing/index.html` to match your preferences

3. **Enable GitHub Pages** in repository settings

4. **Share your docs!**

---

Questions? Check the [doc-gen4 documentation](https://github.com/leanprover/doc-gen4) or open an issue.
