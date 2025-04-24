/**
 * AST Visualization Utilities
 * 
 * This module provides tools to visualize the Abstract Syntax Tree
 * for debugging and educational purposes.
 */

/**
 * Convert an AST to a visualization-friendly format
 * 
 * @param {object} ast - The AST to visualize
 * @return {object} A tree structure suitable for visualization
 */
export function visualizeAST(ast) {
  if (!ast) return null;
  
  function processNode(node, id = 'root') {
    if (!node || typeof node !== 'object') {
      return {
        id,
        name: String(node),
        children: []
      };
    }
    
    const result = {
      id,
      name: node.type || 'Unknown',
      children: []
    };
    
    // Add location information if available
    if (node.location) {
      result.meta = {
        location: {
          line: node.location.start.line,
          column: node.location.start.column
        }
      };
    }
    
    // Add attributes for specific node types
    switch (node.type) {
      case 'Identifier':
        result.attributes = { name: node.name };
        break;
      case 'IntegerLiteral':
      case 'BooleanLiteral':
        result.attributes = { value: node.value };
        break;
      case 'BinaryExpression':
        result.attributes = { operator: node.operator };
        break;
      case 'UnaryExpression':
        result.attributes = { operator: node.operator };
        break;
    }
    
    // Process children based on node type
    Object.keys(node).forEach((key) => {
      // Skip non-AST properties
      if (['type', 'location', 'parent'].includes(key)) return;
      
      const value = node[key];
      
      if (Array.isArray(value)) {
        // Handle arrays (like statements)
        value.forEach((item, i) => {
          if (item && typeof item === 'object') {
            const childId = `${id}-${key}-${i}`;
            result.children.push(processNode(item, childId));
          }
        });
      } else if (value && typeof value === 'object') {
        // Handle nested objects (like expressions)
        const childId = `${id}-${key}`;
        result.children.push(processNode(value, childId));
      } else if (value !== undefined) {
        // Handle primitive values as leaf nodes
        const childId = `${id}-${key}`;
        result.children.push({
          id: childId,
          name: `${key}: ${value}`,
          children: []
        });
      }
    });
    
    return result;
  }
  
  return processNode(ast);
}

/**
 * Generate HTML representation of an AST for visualization
 * 
 * @param {object} ast - The AST to visualize
 * @return {string} HTML string representing the tree
 */
export function generateTreeHTML(ast) {
  const treeData = visualizeAST(ast);
  
  function generateNodeHTML(node) {
    let html = `<li>`;
    html += `<span class="tree-node ${node.name.toLowerCase()}">${node.name}`;
    
    // Add attributes if they exist
    if (node.attributes) {
      const attrStr = Object.entries(node.attributes)
        .map(([k, v]) => `${k}="${v}"`)
        .join(', ');
      html += ` <span class="attributes">(${attrStr})</span>`;
    }
    
    html += `</span>`;
    
    if (node.children && node.children.length > 0) {
      html += `<ul>`;
      node.children.forEach(child => {
        html += generateNodeHTML(child);
      });
      html += `</ul>`;
    }
    
    html += `</li>`;
    return html;
  }
  
  let html = `
    <div class="ast-tree">
      <ul class="tree">
        ${generateNodeHTML(treeData)}
      </ul>
    </div>
    <style>
      .ast-tree {
        font-family: monospace;
      }
      .tree, .tree ul {
        list-style: none;
        padding-left: 1.5em;
      }
      .tree li {
        position: relative;
      }
      .tree-node {
        font-weight: bold;
      }
      .attributes {
        font-weight: normal;
        color: #666;
        font-style: italic;
      }
      .program { color: #1a0dab; }
      .assignmentstatement { color: #006621; }
      .ifstatement, .whilestatement, .forstatement { color: #7928ca; }
      .binaryexpression, .unaryexpression { color: #d32f2f; }
      .identifier { color: #1976d2; }
      .integerliteral, .booleanliteral { color: #e65100; }
      .assertstatement, .postconditionstatement { color: #ad1457; }
    </style>
  `;
  
  return html;
}

/**
 * Generate a DOT representation of the AST for GraphViz
 * 
 * @param {object} ast - The AST to visualize
 * @return {string} DOT language string for GraphViz
 */
export function generateDotGraph(ast) {
  const treeData = visualizeAST(ast);
  const nodes = [];
  const edges = [];
  
  function processNode(node) {
    // Create node definition
    let label = node.name;
    if (node.attributes) {
      const attrs = Object.entries(node.attributes)
        .map(([k, v]) => `${k}: ${v}`)
        .join('\\n');
      label += `\\n(${attrs})`;
    }
    
    nodes.push(`  "${node.id}" [label="${label}"];`);
    
    // Create edges to children
    node.children.forEach(child => {
      edges.push(`  "${node.id}" -> "${child.id}";`);
      processNode(child);
    });
  }
  
  processNode(treeData);
  
  return `digraph AST {\n  node [shape=box, fontname="Arial"];\n${nodes.join('\n')}\n${edges.join('\n')}\n}`;
}

export default {
  visualizeAST,
  generateTreeHTML,
  generateDotGraph
};
