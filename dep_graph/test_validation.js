#!/usr/bin/env node

const fs = require('fs');

// Test 1: Validate test_graph.json schema
console.log('=== Testing test_graph.json ===');
try {
  const graphData = JSON.parse(fs.readFileSync('test_graph.json', 'utf8'));

  // Check required fields
  if (!graphData.nodes || !graphData.edges) {
    throw new Error('Missing nodes or edges');
  }

  console.log(`✓ Valid JSON structure`);
  console.log(`✓ Nodes: ${graphData.nodes.length}`);
  console.log(`✓ Edges: ${graphData.edges.length}`);

  // Validate node schema
  graphData.nodes.forEach((node, i) => {
    const required = ['id', 'label', 'type', 'namespace', 'file', 'line', 'docstring', 'paperRefs', 'isMainTheorem'];
    required.forEach(field => {
      if (!(field in node)) {
        throw new Error(`Node ${i} missing field: ${field}`);
      }
    });
  });
  console.log(`✓ All nodes have required fields`);

  // Validate edge schema
  graphData.edges.forEach((edge, i) => {
    if (!edge.source || !edge.target) {
      throw new Error(`Edge ${i} missing source or target`);
    }
  });
  console.log(`✓ All edges have source and target`);

  // Check edge references
  const nodeIds = new Set(graphData.nodes.map(n => n.id));
  graphData.edges.forEach((edge, i) => {
    if (!nodeIds.has(edge.source)) {
      throw new Error(`Edge ${i} has invalid source: ${edge.source}`);
    }
    if (!nodeIds.has(edge.target)) {
      throw new Error(`Edge ${i} has invalid target: ${edge.target}`);
    }
  });
  console.log(`✓ All edge references are valid`);

  // Check main theorem
  const mainTheorems = graphData.nodes.filter(n => n.isMainTheorem);
  console.log(`✓ Main theorems: ${mainTheorems.length}`);

  // Node type distribution
  const types = {};
  graphData.nodes.forEach(n => {
    types[n.type] = (types[n.type] || 0) + 1;
  });
  console.log(`✓ Node types:`, types);

} catch (error) {
  console.error(`✗ Error:`, error.message);
  process.exit(1);
}

// Test 2: Validate test_positions.json
console.log('\n=== Testing test_positions.json ===');
try {
  const positions = JSON.parse(fs.readFileSync('test_positions.json', 'utf8'));

  console.log(`✓ Valid JSON structure`);
  console.log(`✓ Position entries: ${Object.keys(positions).length}`);

  // Validate position structure
  Object.entries(positions).forEach(([id, pos]) => {
    if (typeof pos.x !== 'number' || typeof pos.y !== 'number') {
      throw new Error(`Invalid position for ${id}: must have x and y numbers`);
    }
  });
  console.log(`✓ All positions have valid x,y coordinates`);

} catch (error) {
  console.error(`✗ Error:`, error.message);
  process.exit(1);
}

console.log('\n=== All tests passed ===');
