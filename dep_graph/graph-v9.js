// GRAPH.JS VERSION 13 - Added statement display and pruned tree filter
console.log('🎨 GRAPH.JS VERSION 13 LOADED - Statement display, pruned tree filter, all previous features');

// Register Cose-Bilkent layout extension with comprehensive debugging
(function() {
  console.log('=== Cytoscape Extension Registration ===');
  console.log('cytoscape available:', typeof cytoscape !== 'undefined');
  console.log('cytoscapeCoseBilkent available:', typeof cytoscapeCoseBilkent !== 'undefined');

  if (typeof cytoscape === 'undefined') {
    console.error('FATAL: Cytoscape core library not loaded');
    return;
  }

  if (typeof cytoscapeCoseBilkent !== 'undefined') {
    cytoscape.use(cytoscapeCoseBilkent);
    console.log('✓ Cose-Bilkent layout registered successfully');
  } else {
    console.warn('⚠ Cose-Bilkent extension not loaded - will fall back to built-in cose layout');
  }
})();

// Global cytoscape instance
let cy;

// Determine which graph file to load (with fallback to test data)
let graphFile = 'graph.json';
if (window.location.search.includes('test')) {
  graphFile = 'test_graph.json';
}

// Fetch data (graph.json and optional positions.json)
Promise.all([
  fetch(graphFile)
    .then(r => {
      if (!r.ok) {
        // Fallback to test_graph.json if main graph.json not found
        if (graphFile === 'graph.json') {
          console.warn('graph.json not found, falling back to test_graph.json');
          return fetch('test_graph.json').then(r2 => {
            if (!r2.ok) throw new Error('Failed to load graph data');
            return r2.json();
          });
        }
        throw new Error(`Failed to load ${graphFile}: ${r.statusText}`);
      }
      return r.json();
    })
    .catch(err => {
      // Handle CORS errors (file:// protocol)
      console.error('Fetch failed (likely CORS):', err);
      return new Promise((resolve) => {
        const loader = document.getElementById('file-loader');
        const input = document.getElementById('graph-file-input');
        loader.style.display = 'block';

        input.addEventListener('change', (e) => {
          const file = e.target.files[0];
          if (file) {
            const reader = new FileReader();
            reader.onload = (e) => {
              loader.style.display = 'none';
              resolve(JSON.parse(e.target.result));
            };
            reader.readAsText(file);
          }
        });
      });
    }),
  fetch('positions.json').then(r => r.ok ? r.json() : {}).catch(() => ({}))
]).then(([graphData, savedPositions]) => {

  // Validate data structure
  if (!graphData.nodes || !graphData.edges) {
    throw new Error('Invalid graph data: missing nodes or edges');
  }

  // Apply saved positions if available
  graphData.nodes.forEach(node => {
    if (savedPositions[node.id]) {
      node.position = savedPositions[node.id];
    }
  });

  // Initialize Cytoscape
  cy = cytoscape({
    container: document.getElementById('cy'),

    elements: {
      nodes: graphData.nodes.map(n => ({ data: n })),
      edges: graphData.edges.map(e => ({ data: e }))
    },

    style: [
      // DEFAULT - All nodes (misc types: constructor, inductive, recursor)
      {
        selector: 'node',
        style: {
          'background-color': '#95A5A6', // Gray for misc
          'shape': 'round-rectangle',  // Unified shape for all nodes
          'label': 'data(label)',
          'font-size': 16,
          'text-wrap': 'wrap',
          'text-max-width': function(node) {
            // Text width based on label length
            const labelLen = node.data('label').length;
            return labelLen * 8;
          },
          'text-valign': 'center',
          'text-halign': 'center',
          'width': function(node) {
            // Box is 10 pixels larger than text
            const labelLen = node.data('label').length;
            const textWidth = labelLen * 8;
            return textWidth + 10;
          },
          'height': function(node) {
            // Height based on width with rectangle aspect ratio
            const labelLen = node.data('label').height;
            const width = labelLen + 10;
            return width;
          },
          'color': '#ffffff',
          'font-weight': 500,
          'text-background-color': '#ffffff',
          'text-background-opacity': 0.0,
          'text-background-padding': '3px'
        }
      },

      // THEOREMS (289 nodes) - Purple/Violet
      {
        selector: 'node[type="theorem"]',
        style: {
          'background-color': '#945ebd'  // removed 'ff' alpha, Cytoscape needs 6-digit format
        }
      },

      // DEFINITIONS (67 nodes) - Teal
      {
        selector: 'node[type="def"]',
        style: {
          'background-color': '#3ab7c4'  // removed 'ff' alpha
        }
      },

      // MAIN THEOREMS (3 nodes) - Muted gold with thick red border (MUST BE LAST)
      {
        selector: '.mainTheorem',
        style: {
          'background-color': '#e0d07a',  // removed 'ff' alpha
          'width': function(node) {
            // Main theorems: 1.3x larger than regular nodes
            const labelLen = node.data('label').length;
            const textWidth = labelLen * 8;
            const baseWidth = textWidth + 10;
            return baseWidth * 1.3;
          },
          'height': function(node) {
            // Main theorems: 1.3x larger with rectangle aspect ratio
            const labelLen = node.data('label').length;
            const textWidth = labelLen * 8;
            const baseWidth = textWidth + 10;
            return baseWidth * 1.3 * 0.45;
          },
          'font-size': 22,
          'font-weight': 'bold',
          'text-max-width': function(node) {
            // Main theorems: text width for larger font
            const labelLen = node.data('label').length;
            return labelLen * 10;  // Slightly larger multiplier for bigger font
          },
          'border-width': 6,
          'border-style': 'double',
          'border-color': '#e0b643'  // removed 'ff' alpha
        }
      },

      // Edge styling
      {
        selector: 'edge',
        style: {
          'width': 2.5,                      // increased from 2
          'line-color': '#95A5A6',
          'target-arrow-color': '#95A5A6',
          'target-arrow-shape': 'triangle',
          'curve-style': 'bezier',
          'arrow-scale': 1.4,                // increased from 1.2
          'opacity': 0.7                     // NEW: slight transparency
        }
      },

      // Highlighted node styling
      {
        selector: 'node.highlighted',
        style: {
          'border-width': 3,
          'border-color': '#FF0000',
          'border-style': 'solid'
        }
      },

      // Faded node styling
      {
        selector: 'node.faded',
        style: {
          'opacity': 0.3
        }
      },

      // Hover state for better interactivity
      {
        selector: 'node:active',
        style: {
          'overlay-color': '#667eea',
          'overlay-opacity': 0.3,
          'overlay-padding': 8
        }
      }
    ],

    layout: {
      name: Object.keys(savedPositions).length > 0 ? 'preset' :
            (typeof cytoscapeCoseBilkent !== 'undefined' ? 'cose-bilkent' : 'cose'),
      idealEdgeLength: 150,    // increased from 150 for much more spacing
      nodeRepulsion: 2000000,    // increased from 12000 for stronger push
      gravity: 0,           // decreased from 0.08 for more spread
      numIter: 1000,
      randomize: true
    }
  });

  // Assign CSS classes to nodes based on data
  cy.nodes().forEach(node => {
    if (node.data('isMainTheorem') === true) {
      node.addClass('mainTheorem');
      console.log('Assigned mainTheorem class to:', node.data('id'));
    }
  });

  // Compute distances from main theorem via backward BFS
  function computeDistancesFromMainTheorem() {
    const mainTheoremId = 'GG5_infinite_at_critical_radius';
    const distances = {};
    const queue = [{id: mainTheoremId, dist: 0}];
    distances[mainTheoremId] = 0;

    while (queue.length > 0) {
      const {id, dist} = queue.shift();
      const incomingEdges = cy.edges(`[target="${id}"]`);

      incomingEdges.forEach(edge => {
        const sourceId = edge.data('source');
        if (!(sourceId in distances)) {
          distances[sourceId] = dist + 1;
          queue.push({id: sourceId, dist: dist + 1});
        }
      });
    }
    return distances;
  }

  // Store distances in node data
  const distances = computeDistancesFromMainTheorem();
  cy.nodes().forEach(node => {
    const dist = distances[node.id()];
    node.data('distanceFromMain', dist !== undefined ? dist : Infinity);
  });
  console.log('Distance computation complete. Sample distances:',
    Object.entries(distances).slice(0, 5).map(([id, d]) => `${id}: ${d}`).join(', '));

  // Click handler - show info panel
  cy.on('tap', 'node', (evt) => {
    const node = evt.target;
    const data = node.data();

    // Populate info panel
    document.getElementById('node-name').textContent = data.id;
    document.getElementById('node-type').textContent = data.type;

    // Statement (GitHub link to view full signature)
    const githubSourceUrl = `https://github.com/e-vergo/TDCSG/blob/main/${data.file}#L${data.line}`;
    document.getElementById('node-statement').innerHTML =
      `<p><strong>Statement:</strong> <a href="${githubSourceUrl}" target="_blank">View source</a></p>`;

    // Docstring
    const docstring = data.docstring || 'No documentation available';
    const truncated = docstring.length > 200 ? docstring.substring(0, 200) + '...' : docstring;
    document.getElementById('node-docstring').innerHTML = `<p><strong>Documentation:</strong></p><p>${truncated}</p>`;

    // Direct dependencies (outgoing edges)
    const dependencies = cy.edges(`[source="${data.id}"]`).map(edge => {
      const targetNode = cy.getElementById(edge.data('target'));
      return {
        id: edge.data('target'),
        label: targetNode.data('label') || edge.data('target')
      };
    });

    if (dependencies.length > 0) {
      let depsHtml = '<p><strong>Direct Dependencies:</strong></p><ul>';
      dependencies.forEach(dep => {
        depsHtml += `<li class="clickable-dep" data-node-id="${dep.id}">${dep.label}</li>`;
      });
      depsHtml += '</ul>';
      document.getElementById('node-dependencies').innerHTML = depsHtml;

      // Add click handlers to dependency list
      document.querySelectorAll('.clickable-dep').forEach(elem => {
        elem.addEventListener('click', () => {
          const targetId = elem.getAttribute('data-node-id');
          const targetNode = cy.getElementById(targetId);
          if (targetNode.length > 0) {
            cy.animate({
              center: { eles: targetNode },
              zoom: 1.5
            }, {
              duration: 500
            });
            // Trigger tap event on the target node
            setTimeout(() => {
              targetNode.trigger('tap');
            }, 500);
          }
        });
      });
    } else {
      document.getElementById('node-dependencies').innerHTML = '';
    }

    // GitHub link
    const githubUrl = `https://github.com/e-vergo/TDCSG/blob/main/${data.file}#L${data.line}`;
    let linksHtml = `<p><strong>Links:</strong></p><ul>`;
    linksHtml += `<li><a href="${githubUrl}" target="_blank">View source on GitHub (line ${data.line})</a></li>`;
    if (data.paperRefs && data.paperRefs.length > 0) {
      linksHtml += `<li>Paper: ${data.paperRefs.join(', ')}</li>`;
    }
    linksHtml += `</ul>`;
    document.getElementById('node-links').innerHTML = linksHtml;
  });

  // Save layout
  document.getElementById('save-layout').addEventListener('click', () => {
    const positions = {};
    cy.nodes().forEach(node => {
      positions[node.id()] = node.position();
    });

    const blob = new Blob([JSON.stringify(positions, null, 2)], {type: 'application/json'});
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'positions.json';
    a.click();
    URL.revokeObjectURL(url);
  });

  // Reset zoom
  document.getElementById('reset-zoom').addEventListener('click', () => {
    cy.fit();
  });

  // Filter functionality
  function applyFilter() {
    const mode = document.getElementById('filter-mode').value;
    const distance = parseInt(document.getElementById('distance-slider').value);
    let visibleNodes = new Set();

    if (mode === 'all') {
      cy.nodes().forEach(n => visibleNodes.add(n.id()));
      document.getElementById('distance-controls').style.display = 'none';
    }
    else if (mode === 'proof-focus') {
      document.getElementById('distance-controls').style.display = 'block';
      cy.nodes().forEach(node => {
        const dist = node.data('distanceFromMain');
        const isMain = node.data('isMainTheorem');
        const isDef = node.data('type') === 'def';
        const inDegree = cy.edges(`[target="${node.id()}"]`).length;

        // Include: main theorems + within distance + high-centrality defs (in-degree >= 40)
        if (isMain || dist <= distance || (isDef && inDegree >= 40)) {
          visibleNodes.add(node.id());
        }
      });
    }
    else if (mode === 'theorems-only') {
      document.getElementById('distance-controls').style.display = 'none';
      cy.nodes('[type="theorem"]').forEach(n => visibleNodes.add(n.id()));
    }
    else if (mode === 'definitions-only') {
      document.getElementById('distance-controls').style.display = 'none';
      cy.nodes('[type="def"]').forEach(n => visibleNodes.add(n.id()));
    }
    else if (mode === 'pruned-tree') {
      document.getElementById('distance-controls').style.display = 'none';
      cy.nodes().forEach(node => {
        const inDegree = cy.edges(`[target="${node.id()}"]`).length;
        // Include nodes with at least one incoming edge, OR main theorems
        if (inDegree > 0 || node.data('isMainTheorem')) {
          visibleNodes.add(node.id());
        }
      });
    }

    // Apply visibility using Cytoscape's hide/show methods
    cy.nodes().forEach(node => {
      if (visibleNodes.has(node.id())) {
        node.show();
      } else {
        node.hide();
      }
    });

    // Update count
    document.getElementById('visible-count').textContent = visibleNodes.size;

    // Re-run layout if >50% nodes hidden
    if (visibleNodes.size < cy.nodes().length * 0.5) {
      cy.layout({
        name: typeof cytoscapeCoseBilkent !== 'undefined' ? 'cose-bilkent' : 'cose',
        idealEdgeLength: 200,    // increased from 150 for much more spacing
        nodeRepulsion: 20000,    // increased from 12000 for stronger push
        gravity: 0.05,           // decreased from 0.08 for more spread
        numIter: 500,
        animate: true,
        animationDuration: 1000
      }).run();
    } else {
      cy.fit();
    }
  }

  document.getElementById('filter-mode').addEventListener('change', applyFilter);
  document.getElementById('distance-slider').addEventListener('input', (e) => {
    document.getElementById('distance-value').textContent = e.target.value;
    applyFilter();
  });

  // Search functionality
  document.getElementById('search').addEventListener('input', (e) => {
    const query = e.target.value.toLowerCase();

    if (!query) {
      cy.nodes().removeClass('faded highlighted');
      return;
    }

    cy.nodes().forEach(node => {
      const label = node.data('label').toLowerCase();
      const id = node.data('id').toLowerCase();

      if (label.includes(query) || id.includes(query)) {
        node.addClass('highlighted');
        node.removeClass('faded');
      } else {
        node.addClass('faded');
        node.removeClass('highlighted');
      }
    });
  });

  // Stats display
  const nodeCount = cy.nodes().length;
  const edgeCount = cy.edges().length;
  document.getElementById('stats').textContent = `${nodeCount} nodes, ${edgeCount} edges`;

  // Initial fit
  cy.fit();

}).catch(error => {
  console.error('Error loading graph:', error);
  document.getElementById('error-text').textContent = error.message;
  document.getElementById('error-message').style.display = 'block';
  document.getElementById('container').style.display = 'none';
  document.getElementById('controls').style.display = 'none';
});
