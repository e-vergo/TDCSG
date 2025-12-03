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
      // Node base styling
      {
        selector: 'node',
        style: {
          'label': 'data(label)',
          'font-size': 14,
          'text-wrap': 'wrap',
          'text-max-width': 80,
          'text-valign': 'center',
          'text-halign': 'center',
          'width': 80,
          'height': 60,
          'color': '#333',
          'font-weight': 500
        }
      },

      // Theorem styling
      {
        selector: 'node[type="theorem"]',
        style: {
          'background-color': '#FF6B6B',
          'shape': 'ellipse'
        }
      },

      // Definition styling
      {
        selector: 'node[type="def"]',
        style: {
          'background-color': '#4ECDC4',
          'shape': 'rectangle'
        }
      },

      // Lemma styling
      {
        selector: 'node[type="lemma"]',
        style: {
          'background-color': '#FFA07A',
          'shape': 'ellipse'
        }
      },

      // Inductive styling
      {
        selector: 'node[type="inductive"]',
        style: {
          'background-color': '#FFD93D',
          'shape': 'diamond'
        }
      },

      // Constructor styling
      {
        selector: 'node[type="constructor"]',
        style: {
          'background-color': '#9B59B6',
          'shape': 'rectangle'
        }
      },

      // Recursor styling
      {
        selector: 'node[type="recursor"]',
        style: {
          'background-color': '#E67E22',
          'shape': 'rectangle'
        }
      },

      // Main theorem special styling
      {
        selector: 'node[isMainTheorem]',
        style: {
          'background-color': '#FFD93D',
          'width': 120,
          'height': 80,
          'font-size': 18,
          'font-weight': 'bold',
          'border-width': 4,
          'border-color': '#FF6B6B'
        }
      },

      // Edge styling
      {
        selector: 'edge',
        style: {
          'width': 2,
          'line-color': '#95A5A6',
          'target-arrow-color': '#95A5A6',
          'target-arrow-shape': 'triangle',
          'curve-style': 'bezier',
          'arrow-scale': 1.2
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
      }
    ],

    layout: {
      name: Object.keys(savedPositions).length > 0 ? 'preset' :
            (typeof cytoscapeCoseBilkent !== 'undefined' ? 'cose-bilkent' : 'cose'),
      idealEdgeLength: 100,
      nodeRepulsion: 8000,
      gravity: 0.1,
      numIter: 1000,
      randomize: true
    }
  });

  // Click handler - show info panel
  cy.on('tap', 'node', (evt) => {
    const node = evt.target;
    const data = node.data();

    // Populate info panel
    document.getElementById('node-name').textContent = data.id;
    document.getElementById('node-type').textContent = data.type;

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

    document.getElementById('info-panel').style.display = 'block';
  });

  // Close panel
  document.getElementById('close-panel').addEventListener('click', () => {
    document.getElementById('info-panel').style.display = 'none';
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
