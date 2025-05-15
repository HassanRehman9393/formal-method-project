import { CFGNode, CFGEdge } from '../../types/visualization';

/**
 * Generates a control flow graph from an abstract syntax tree
 * @param {any} ast The abstract syntax tree
 * @param {boolean} isSSA Whether to generate SSA-based CFG
 * @returns Object containing nodes and edges for the CFG
 */
export function generateCFG(ast: any, isSSA: boolean = false): { nodes: CFGNode[], edges: CFGEdge[] } {
  // Return a minimal empty graph when no AST is provided
  if (!ast) {
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
  
  // State for tracking nodes and edges
  const nodes: CFGNode[] = [];
  const edges: CFGEdge[] = [];
  
  // Add entry node
  const entryNode: CFGNode = {
    id: 'entry',
    label: 'START',
    type: 'entry',
    code: 'Program entry point'
  };
  nodes.push(entryNode);
  
  // Add exit node
  const exitNode: CFGNode = {
    id: 'exit',
    label: 'END',
    type: 'exit',
    code: 'Program exit point'
  };
  
  // Process the AST to create nodes and edges
  if (ast.type === 'Program' && ast.body && Array.isArray(ast.body)) {
    let lastNodeId = 'entry';
    
    // Process each statement in the program body
    ast.body.forEach((statement: any, index: number) => {
      const nodeId = `stmt_${index}`;
      const label = getStatementLabel(statement);
      const type = getStatementType(statement);
      const code = getStatementCode(statement, isSSA);
      
      // Create node for this statement
      const node: CFGNode = {
        id: nodeId,
        label,
        type,
        code
      };
      nodes.push(node);
      
      // Create edge from previous statement to this one
      edges.push({
        source: lastNodeId,
        target: nodeId,
        label: '',
        isHighlighted: false
      });
      
      // Handle if statements with branches
      if (statement.type === 'IfStatement') {
        // Create nodes for then and else branches
        const thenNodeId = `then_${index}`;
        const elseNodeId = `else_${index}`;
        const joinNodeId = `join_${index}`;
        
        // Create then branch node
        nodes.push({
          id: thenNodeId,
          label: 'Then Branch',
          type: 'statement',
          code: getStatementCode(statement.consequent, isSSA)
        });
        
        // Create else branch node if it exists
        if (statement.alternate) {
          nodes.push({
            id: elseNodeId,
            label: 'Else Branch',
            type: 'statement',
            code: getStatementCode(statement.alternate, isSSA)
          });
        }
        
        // Create join node
        nodes.push({
          id: joinNodeId,
          label: 'Join',
          type: 'join',
          code: 'Control flow joins here'
        });
        
        // Create edges for branches
        edges.push({
          source: nodeId,
          target: thenNodeId,
          label: 'true',
          isHighlighted: false
        });
        
        if (statement.alternate) {
          edges.push({
            source: nodeId,
            target: elseNodeId,
            label: 'false',
            isHighlighted: false
          });
          
          edges.push({
            source: elseNodeId,
            target: joinNodeId,
            label: '',
            isHighlighted: false
          });
        } else {
          edges.push({
            source: nodeId,
            target: joinNodeId,
            label: 'false',
            isHighlighted: false
          });
        }
        
        edges.push({
          source: thenNodeId,
          target: joinNodeId,
          label: '',
          isHighlighted: false
        });
        
        // Update last node ID to the join node
        lastNodeId = joinNodeId;
      } else {
        // For simple statements, just update the last node ID
        lastNodeId = nodeId;
      }
      
      // Special handling for assert statements
      if (statement.type === 'AssertStatement') {
        // Create a branch for assert failure
        const failNodeId = `fail_${index}`;
        
        // Create fail node
        nodes.push({
          id: failNodeId,
          label: 'Assertion Failed',
          type: 'exit',
          code: 'Program terminated due to failed assertion'
        });
        
        // Create edge to the fail node
        edges.push({
          source: nodeId,
          target: failNodeId,
          label: 'false',
          isHighlighted: false
        });
      }
    });
    
    // Connect last statement to exit
    edges.push({
      source: lastNodeId,
      target: 'exit',
      label: '',
      isHighlighted: false
    });
  } else {
    // If the AST doesn't have the expected structure, connect entry directly to exit
    edges.push({
      source: 'entry',
      target: 'exit',
      label: '',
      isHighlighted: false
    });
  }
  
  // Add exit node at the end
  nodes.push(exitNode);
  
  return { nodes, edges };
}

/**
 * Get a readable label for a statement
 */
function getStatementLabel(statement: any): string {
  if (!statement) return 'Unknown';
  
  switch (statement.type) {
    case 'VariableDeclaration':
      return statement.id?.name 
        ? `${statement.id.name} := ...` 
        : 'var := ...';
    case 'AssignmentStatement':
      return statement.left?.name 
        ? `${statement.left.name} := ...` 
        : 'assign';
    case 'IfStatement':
      return 'if (...)';
    case 'WhileStatement':
      return 'while (...)';
    case 'ForStatement':
      return 'for (...)';
    case 'AssertStatement':
      return 'assert(...)';
    case 'BinaryExpression':
      return `${statement.operator || '?'}`;
    default:
      return statement.type || 'Statement';
  }
}

/**
 * Get the node type based on statement type
 */
function getStatementType(statement: any): "entry" | "exit" | "statement" | "condition" | "join" | "assert" {
  if (!statement) return "statement";
  
  switch (statement.type) {
    case 'IfStatement':
    case 'WhileStatement':
    case 'ForStatement':
      return "condition";
    case 'AssertStatement':
      return "assert";
    default:
      return "statement";
  }
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
  
  switch (statement.type) {
    case 'VariableDeclaration':
      if (statement.id && statement.init) {
        const varName = statement.id.name || '?';
        const initValue = expressionToString(statement.init);
        return `${varName} := ${initValue}`;
      }
      return 'var := value';
      
    case 'AssignmentStatement':
      if (statement.left && statement.right) {
        const leftStr = statement.left.name || '?';
        const rightStr = expressionToString(statement.right);
        return `${leftStr} := ${rightStr}`;
      }
      return 'x := y';
      
    case 'AssertStatement':
      if (statement.expression) {
        return `assert(${expressionToString(statement.expression)})`;
      }
      return 'assert(...)';
      
    case 'IfStatement':
      return `if (${expressionToString(statement.condition)})`;
      
    case 'WhileStatement':
      return `while (${expressionToString(statement.condition)})`;
      
    default:
      return statement.type ? `${statement.type}` : 'Statement';
  }
}

/**
 * Convert an expression to a string
 */
function expressionToString(expr: any): string {
  if (!expr) return '?';
  
  switch (expr.type) {
    case 'Identifier':
      return expr.name || '?';
      
    case 'Literal':
      return expr.value?.toString() || '?';
      
    case 'BinaryExpression':
      return `${expressionToString(expr.left)} ${expr.operator || '?'} ${expressionToString(expr.right)}`;
      
    default:
      return expr.type ? `${expr.type}` : '?';
  }
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
