import { CFGNode, CFGEdge } from '../../types/visualization';

/**
 * Generates a control flow graph from an abstract syntax tree
 * @param {any} ast The abstract syntax tree
 * @param {boolean} isSSA Whether to generate SSA-based CFG
 * @returns Object containing nodes and edges for the CFG
 */
export function generateCFG(ast: any, isSSA: boolean = false): { nodes: CFGNode[], edges: CFGEdge[] } {
  // Now using the ast parameter properly
  if (!ast) {
    // Return a minimal empty graph when no AST is provided
    return {
      nodes: [
        {
          id: 'empty',
          label: 'No AST Available',
          type: 'entry',
          code: 'No code to display'
        }
      ],
      edges: []
    };
  }
  
  // Process the AST to create nodes
  const nodes: CFGNode[] = processAstNodes(ast, isSSA);
  
  // Generate edges based on the AST structure
  const edges: CFGEdge[] = generateEdgesFromAst(ast);
  
  return { nodes, edges };
}

/**
 * Process the AST and generate CFG nodes
 */
function processAstNodes(ast: any, isSSA: boolean): CFGNode[] {
  // Start with an entry node
  const nodes: CFGNode[] = [
    {
      id: 'entry',
      label: 'START',
      type: 'entry',
      code: 'Program entry point'
    }
  ];
  
  // Example node processing logic - this would be expanded based on the actual AST structure
  if (ast && ast.body && Array.isArray(ast.body)) {
    ast.body.forEach((statement: any, index: number) => {
      const nodeId = `n${index + 1}`;
      nodes.push({
        id: nodeId,
        label: getStatementLabel(statement),
        type: getStatementType(statement),
        code: getStatementCode(statement, isSSA)
      });
    });
  }
  
  // Add exit node
  nodes.push({
    id: 'exit',
    label: 'END',
    type: 'exit',
    code: 'Program exit point'
  });
  
  return nodes;
}

/**
 * Generate edges based on the AST structure
 */
function generateEdgesFromAst(ast: any): CFGEdge[] {
  const edges: CFGEdge[] = [];
  
  // Example edge creation logic
  if (ast && ast.body && Array.isArray(ast.body)) {
    // Connect entry to first statement
    edges.push({
      source: 'entry',
      target: 'n1',
      label: '',
      isHighlighted: false
    });
    
    // Connect statements sequentially
    ast.body.forEach((_: any, index: number) => {
      // Removed the unused statement parameter and replaced with _
      if (index < ast.body.length - 1) {
        edges.push({
          source: `n${index + 1}`,
          target: `n${index + 2}`,
          label: '',
          isHighlighted: false
        });
      }
    });
    
    // Connect last statement to exit
    if (ast.body.length > 0) {
      edges.push({
        source: `n${ast.body.length}`,
        target: 'exit',
        label: '',
        isHighlighted: false
      });
    } else {
      // If no statements, connect entry directly to exit
      edges.push({
        source: 'entry',
        target: 'exit',
        label: '',
        isHighlighted: false
      });
    }
  }
  
  return edges;
}

/**
 * Get a readable label for a statement
 */
function getStatementLabel(statement: any): string {
  if (!statement) return 'Unknown';
  
  if (statement.type === 'IfStatement') return 'if';
  if (statement.type === 'WhileStatement') return 'while';
  if (statement.type === 'ForStatement') return 'for';
  if (statement.type === 'AssignmentStatement') return 'assign';
  if (statement.type === 'AssertStatement') return 'assert';
  
  return statement.type || 'Statement';
}

/**
 * Get the node type based on statement type
 */
function getStatementType(statement: any): "entry" | "exit" | "statement" | "condition" | "join" | "assert" {
  if (!statement) return "statement";
  
  if (statement.type === 'IfStatement') return "condition";
  if (statement.type === 'WhileStatement') return "condition";
  if (statement.type === 'ForStatement') return "condition";
  if (statement.type === 'AssertStatement') return "assert";
  
  return "statement";  // Return "statement" as the default type
}

/**
 * Get code representation for a statement
 */
function getStatementCode(statement: any, isSSA: boolean): string {
  if (!statement) return 'Unknown statement';
  
  // For SSA form, we might want to show a different representation
  if (isSSA && statement.ssaForm) {
    return statement.ssaForm;
  }
  
  // This would be replaced with actual code generation based on the statement
  return statement.type ? `${statement.type} statement` : 'Statement';
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
  if (!cfg || !path || path.length === 0) return cfg;
  
  // Create a deep copy of the CFG
  const newNodes = cfg.nodes.map(node => ({
    ...node,
    isHighlighted: path.includes(node.id)
  }));
  
  // Highlight edges that connect nodes in the path
  const newEdges = cfg.edges.map(edge => {
    // Fix the type issue by ensuring we're working with string sources and targets
    const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
    const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
    
    const sourceInPath = path.includes(sourceId);
    const targetInPath = path.includes(targetId);
    const isConsecutive = path.findIndex(id => id === sourceId) + 1 === path.findIndex(id => id === targetId);
    
    return {
      ...edge,
      isHighlighted: sourceInPath && targetInPath && isConsecutive
    };
  });
  
  return { nodes: newNodes, edges: newEdges };
}
