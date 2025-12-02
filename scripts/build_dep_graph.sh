#!/bin/bash
set -e

cd /Users/eric/Documents/GitHub/TDCSG

echo "=== Building TDCSG Dependency Graph ==="
mkdir -p docs

# 1. Extract dependencies
echo "Step 1/4: Extracting dependencies..."
lake exe extract_dep_graph > docs/deps.dot

# 2. Validate and generate static SVG
echo "Step 2/4: Validating and generating static SVG..."
if command -v dot >/dev/null 2>&1; then
    dot -Tsvg docs/deps.dot > /dev/null && echo "  ✓ Valid"
    dot -Tsvg docs/deps.dot -o docs/deps_static.svg && echo "  ✓ Static SVG generated"
else
    echo "  ⚠ graphviz not found, skipping static SVG"
fi

# 3. Generate HTML with embedded DOT
echo "Step 3/4: Generating HTML..."

# Read and escape DOT content
DOT_CONTENT=$(cat docs/deps.dot | sed 's/\\/\\\\/g' | sed 's/`/\\`/g' | sed 's/\$/\\$/g')

# Generate complete HTML file with embedded DOT
cat > docs/dep_graph.html << END_OF_HTML
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>TDCSG Dependency Graph</title>
  <script src="https://d3js.org/d3.v7.min.js"></script>
  <script src="https://unpkg.com/@hpcc-js/wasm/dist/graphviz.umd.js"></script>
  <script src="https://unpkg.com/d3-graphviz@5.0.2/build/d3-graphviz.min.js"></script>
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; background: #f5f5f5; overflow: hidden; }
    #controls { position: fixed; top: 20px; right: 20px; background: white; padding: 15px; border-radius: 8px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); z-index: 1000; display: flex; flex-direction: column; gap: 10px; min-width: 250px; }
    #controls input[type="text"] { width: 100%; padding: 8px 12px; border: 1px solid #ddd; border-radius: 4px; font-size: 14px; }
    #controls input[type="text"]:focus { outline: none; border-color: #4CAF50; }
    #controls button { padding: 8px 12px; background: #4CAF50; color: white; border: none; border-radius: 4px; cursor: pointer; font-size: 14px; transition: background 0.2s; }
    #controls button:hover { background: #45a049; }
    #graph { width: 100vw; height: 100vh; cursor: grab; }
    #graph:active { cursor: grabbing; }
    #legend { position: fixed; bottom: 20px; left: 20px; background: white; padding: 15px; border-radius: 8px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); z-index: 1000; font-size: 12px; }
    #legend h3 { margin: 0 0 10px 0; font-size: 14px; font-weight: 600; }
    #legend .legend-section { margin-bottom: 10px; }
    #legend .legend-section:last-child { margin-bottom: 0; }
    #legend .legend-title { font-weight: 600; margin-bottom: 5px; color: #333; }
    #legend .legend-item { display: flex; align-items: center; gap: 8px; margin: 4px 0; color: #666; }
    #legend .shape-demo, #legend .color-demo { width: 20px; height: 15px; border: 1px solid #666; flex-shrink: 0; }
    .highlight { stroke: red !important; stroke-width: 3px !important; }
    #stats { margin-top: 10px; padding-top: 10px; border-top: 1px solid #eee; font-size: 11px; color: #999; }
    #loading { position: fixed; top: 50%; left: 50%; transform: translate(-50%, -50%); background: white; padding: 30px 40px; border-radius: 8px; box-shadow: 0 4px 20px rgba(0,0,0,0.15); z-index: 2000; text-align: center; }
    #loading .spinner { border: 3px solid #f3f3f3; border-top: 3px solid #4CAF50; border-radius: 50%; width: 40px; height: 40px; animation: spin 1s linear infinite; margin: 0 auto 15px; }
    @keyframes spin { 0% { transform: rotate(0deg); } 100% { transform: rotate(360deg); } }
    #loading-text { color: #666; font-size: 14px; }
  </style>
</head>
<body>
  <div id="loading">
    <div class="spinner"></div>
    <div id="loading-text">Loading graph (767 declarations)...</div>
    <div id="fallback-hint" style="display: none; margin-top: 15px; font-size: 12px; color: #666;">
      Taking a while? Try the <a href="deps_static.svg" target="_blank" style="color: #4CAF50;">static SVG version</a>
    </div>
  </div>
  <div id="controls">
    <input type="text" id="search" placeholder="Search (e.g., r_crit, φ)...">
    <button id="reset">Reset Zoom</button>
    <button id="fit">Fit to Screen</button>
    <button id="static">View Static SVG</button>
    <div id="stats"></div>
  </div>
  <div id="graph"></div>
  <div id="legend">
    <h3>TDCSG Dependency Graph</h3>
    <div class="legend-section">
      <div class="legend-title">Shapes</div>
      <div class="legend-item"><div class="shape-demo" style="border-radius: 50%;"></div><span>Theorem/Lemma</span></div>
      <div class="legend-item"><div class="shape-demo"></div><span>Definition</span></div>
      <div class="legend-item"><div class="shape-demo" style="transform: rotate(45deg);"></div><span>Inductive</span></div>
    </div>
    <div class="legend-section">
      <div class="legend-title">Colors (All Formalized)</div>
      <div class="legend-item"><div class="color-demo" style="background: #90EE90;"></div><span>Definitions</span></div>
      <div class="legend-item"><div class="color-demo" style="background: #7CFC00;"></div><span>CompoundSymmetry</span></div>
      <div class="legend-item"><div class="color-demo" style="background: #98FB98;"></div><span>Proofs</span></div>
    </div>
  </div>
  <script>
    const dotString = \`${DOT_CONTENT}\`;
    const nodeCount = (dotString.match(/\[shape=/g) || []).length;
    const edgeCount = (dotString.match(/->/g) || []).length;
    document.getElementById('stats').textContent = \`\${nodeCount} declarations, \${edgeCount} dependencies\`;

    console.log('Initializing graphviz...');
    console.log(\`DOT string length: \${dotString.length} chars\`);
    console.log(\`Parsed: \${nodeCount} nodes, \${edgeCount} edges\`);

    const loadingEl = document.getElementById('loading');
    const loadingText = document.getElementById('loading-text');
    const fallbackHint = document.getElementById('fallback-hint');

    // Show fallback hint after 10 seconds
    setTimeout(() => {
      if (loadingEl.style.display !== 'none') {
        fallbackHint.style.display = 'block';
      }
    }, 10000);

    document.getElementById('static').addEventListener('click', () => {
      window.open('deps_static.svg', '_blank');
    });

    try {
      loadingText.textContent = 'Initializing Graphviz...';

      const graphviz = d3.select("#graph")
        .graphviz({useWorker: false})  // Disable worker for better error messages
        .zoom(true)
        .fit(true)
        .engine("dot")
        .width(window.innerWidth)
        .height(window.innerHeight)
        .on("initEnd", () => {
          console.log("Graphviz initialized");
          loadingText.textContent = 'Rendering graph (this may take a minute)...';
        })
        .on("start", () => {
          console.log("Rendering started...");
          loadingText.textContent = 'Rendering graph...';
        })
        .on("end", () => {
          console.log("Rendering complete!");
          loadingEl.style.display = 'none';
        });

      console.log("Starting render...");
      graphviz.renderDot(dotString);

      let searchTimeout;
      document.getElementById('search').addEventListener('input', function(e) {
        clearTimeout(searchTimeout);
        searchTimeout = setTimeout(() => {
          const query = e.target.value.toLowerCase().trim();
          document.querySelectorAll('.highlight').forEach(el => el.classList.remove('highlight'));
          if (query) {
            document.querySelectorAll('.node title').forEach(title => {
              if (title.textContent.toLowerCase().includes(query)) {
                const ellipse = title.parentElement.querySelector('ellipse, polygon, path');
                if (ellipse) ellipse.classList.add('highlight');
              }
            });
          }
        }, 300);
      });

      document.getElementById('reset').addEventListener('click', () => graphviz.resetZoom());
      document.getElementById('fit').addEventListener('click', () => graphviz.fit(true).render());
      window.addEventListener('resize', () => graphviz.width(window.innerWidth).height(window.innerHeight).render());
      document.getElementById('graph').addEventListener('contextmenu', e => e.preventDefault());
    } catch (error) {
      console.error("Error initializing graphviz:", error);
      loadingEl.style.display = 'none';
      document.getElementById('graph').innerHTML = '<div style="padding: 20px; color: red;">Error loading graph: ' + error.message + '</div>';
    }
  </script>
</body>
</html>
END_OF_HTML

echo "Step 4/4: Complete!"
echo "=== Complete! ==="
echo "Files: docs/deps.dot, docs/deps_static.svg, docs/dep_graph.html"
echo "View: open docs/dep_graph.html"
echo "      open docs/deps_static.svg  (fallback for large graph)"
