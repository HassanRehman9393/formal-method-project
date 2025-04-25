import { CFGNode, CFGEdge } from '../../types/visualization';

/**
 * Generates a control flow graph from an abstract syntax tree
 * @param {any} ast The abstract syntax tree
 * @param {boolean} isSSA Whether to generate SSA-based CFG
 * @returns Object containing nodes and edges for the CFG
 */
export function generateCFG(_ast: any, isSSA: boolean = false): { nodes: CFGNode[], edges: CFGEdge[] } {
  // Renamed 'ast' parameter to '_ast' to indicate it's not used yet
  
  // Create a simple example CFG
  const nodes: CFGNode[] = [
    {
      id: 'entry',
      label: 'START',
      type: 'entry',
      code: 'Program entry point'
    },
    {
      id: 'n1',
      label: isSSA ? 'x_0 := 0' : 'x := 0',
      type: 'statement',
      code: isSSA ? 'x_0 := 0' : 'x := 0',
      line: 1
    },
    {
      id: 'n2',
      label: isSSA ? 'i_0 := 0' : 'i := 0',
      type: 'statement',
      code: isSSA ? 'i_0 := 0' : 'i := 0',
      line: 2
    },
    {
      id: 'loop_cond',
      label: isSSA ? 'i_phi < 10' : 'i < 10',
      type: 'condition',
      code: isSSA ? 'i_phi < 10' : 'i < 10',
      line: 3
    },
    {
      id: 'loop_body1',
      label: isSSA ? 'i_1 := i_phi + 1' : 'i := i + 1',
      type: 'statement',
      code: isSSA ? 'i_1 := i_phi + 1' : 'i := i + 1',
      line: 4
    },
    {
      id: 'loop_body2',
      label: isSSA ? 'x_1 := x_phi + i_1' : 'x := x + i',
      type: 'statement',
      code: isSSA ? 'x_1 := x_phi + i_1' : 'x := x + i',
      line: 5
    },
    {
      id: 'phi_node',
      label: isSSA ? 'x_phi := φ(x_0, x_1), i_phi := φ(i_0, i_1)' : 'Loop join',
      type: 'join',
      code: isSSA ? 'x_phi := φ(x_0, x_1)\ni_phi := φ(i_0, i_1)' : 'Loop join point',
      line: 6
    },
    {
      id: 'assert',
      label: isSSA ? 'assert(x_phi >= 0)' : 'assert(x >= 0)',
      type: 'statement',
      code: isSSA ? 'assert(x_phi >= 0)' : 'assert(x >= 0)',
      line: 7
    },
    {
      id: 'exit',
      label: 'END',
      type: 'exit',
      code: 'Program exit point'
    }
  ];

  const edges: CFGEdge[] = [
    { source: 'entry', target: 'n1' },
    { source: 'n1', target: 'n2' },
    { source: 'n2', target: 'phi_node' },
    { source: 'phi_node', target: 'loop_cond' },
    { source: 'loop_cond', target: 'loop_body1', condition: 'true' },
    { source: 'loop_cond', target: 'assert', condition: 'false' },
    { source: 'loop_body1', target: 'loop_body2' },
    { source: 'loop_body2', target: 'phi_node' },
    { source: 'assert', target: 'exit' }
  ];

  return { nodes, edges };
}

/**
 * Highlights a specific path in a CFG
 * @param cfg The control flow graph
 * @param path Array of node IDs to highlight
 * @returns New CFG with highlighted nodes and edges
 */
export function highlightPath(
  cfg: { nodes: CFGNode[], edges: CFGEdge[] },
  path: string[]
): { nodes: CFGNode[], edges: CFGEdge[] } {
  if (!cfg || !path || path.length === 0) {
    return cfg;
  }

  const newNodes = cfg.nodes.map(node => ({
    ...node,
    isHighlighted: path.includes(node.id)
  }));

  const newEdges = cfg.edges.map(edge => {
    const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
    const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
    
    // Highlight if edge connects consecutive nodes in the path
    const sourceIndex = path.indexOf(sourceId);
    const targetIndex = path.indexOf(targetId);
    const isHighlighted = sourceIndex !== -1 && 
                           targetIndex !== -1 && 
                           Math.abs(sourceIndex - targetIndex) === 1;
    
    return { ...edge, isHighlighted };
  });

  return { nodes: newNodes, edges: newEdges };
}
