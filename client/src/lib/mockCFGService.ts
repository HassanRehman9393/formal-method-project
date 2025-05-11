/**
 * Mock Control Flow Graph Service
 * Provides mock CFG generation for development and testing
 */

/**
 * Generate a mock Control Flow Graph for display
 * @param program The source program
 * @param ast Optional AST to use for CFG generation
 * @param ssaAst Optional SSA AST to use for CFG generation
 * @returns Mock CFG data suitable for visualization
 */
export const generateMockCFG = (
  program: string,
  ast?: any,
  ssaAst?: any
): {
  nodes: CFGNode[];
  edges: CFGEdge[];
  entryNode: string;
  exitNode: string;
} => {
  try {
    // Extract some basic information from the program
    const hasIfStatement = program.includes('if');
    const hasLoop = program.includes('while') || program.includes('for');
    const hasAssert = program.includes('assert');
    
    // Create a basic set of nodes and edges
    const nodes: CFGNode[] = [];
    const edges: CFGEdge[] = [];
    
    // Always add entry and exit nodes
    nodes.push(createNode('Entry', 'entry', 'Entry point'));
    
    // Add basic variable declaration nodes
    const variableMatches = program.match(/(\w+)\s*:=\s*([^;]+);/g) || [];
    
    variableMatches.forEach((match, index) => {
      const nodeId = `var_${index}`;
      nodes.push(createNode(match.trim(), nodeId, 'Variable declaration'));
      
      // Connect to previous node or entry
      if (index === 0) {
        edges.push(createEdge('entry', nodeId, ''));
      } else {
        edges.push(createEdge(`var_${index - 1}`, nodeId, ''));
      }
    });
    
    // Add conditional nodes if detected
    if (hasIfStatement) {
      const conditionNodeId = 'condition_1';
      nodes.push(createNode('if (condition)', conditionNodeId, 'Conditional statement'));
      
      // Connect last variable node to condition
      if (variableMatches.length > 0) {
        edges.push(createEdge(`var_${variableMatches.length - 1}`, conditionNodeId, ''));
      } else {
        edges.push(createEdge('entry', conditionNodeId, ''));
      }
      
      // Add true branch
      const trueNodeId = 'true_branch';
      nodes.push(createNode('True branch', trueNodeId, 'If branch'));
      edges.push(createEdge(conditionNodeId, trueNodeId, 'true'));
      
      // Add false branch
      const falseNodeId = 'false_branch';
      nodes.push(createNode('False branch', falseNodeId, 'Else branch'));
      edges.push(createEdge(conditionNodeId, falseNodeId, 'false'));
      
      // After branches
      const afterIfNodeId = 'after_if';
      nodes.push(createNode('After if', afterIfNodeId, 'Code after if statement'));
      edges.push(createEdge(trueNodeId, afterIfNodeId, ''));
      edges.push(createEdge(falseNodeId, afterIfNodeId, ''));
      
      // Connect to exit
      edges.push(createEdge(afterIfNodeId, 'exit', ''));
    } else if (hasLoop) {
      // Add loop node
      const loopNodeId = 'loop_1';
      nodes.push(createNode('while (condition)', loopNodeId, 'Loop statement'));
      
      // Connect last variable node to loop
      if (variableMatches.length > 0) {
        edges.push(createEdge(`var_${variableMatches.length - 1}`, loopNodeId, ''));
      } else {
        edges.push(createEdge('entry', loopNodeId, ''));
      }
      
      // Add loop body
      const loopBodyId = 'loop_body';
      nodes.push(createNode('Loop body', loopBodyId, 'Loop body'));
      edges.push(createEdge(loopNodeId, loopBodyId, 'true'));
      
      // Loop back
      edges.push(createEdge(loopBodyId, loopNodeId, 'back'));
      
      // After loop
      const afterLoopId = 'after_loop';
      nodes.push(createNode('After loop', afterLoopId, 'Code after loop'));
      edges.push(createEdge(loopNodeId, afterLoopId, 'false'));
      
      // Connect to exit
      edges.push(createEdge(afterLoopId, 'exit', ''));
    } else {
      // Connect last variable node to exit
      if (variableMatches.length > 0) {
        edges.push(createEdge(`var_${variableMatches.length - 1}`, 'exit', ''));
      } else {
        edges.push(createEdge('entry', 'exit', ''));
      }
    }
    
    // Add assert if present
    if (hasAssert) {
      const assertNodeId = 'assert_1';
      nodes.push(createNode('assert(condition)', assertNodeId, 'Assertion'));
      
      // Update connections to include assert before exit
      edges.forEach(edge => {
        if (edge.target === 'exit') {
          edge.target = assertNodeId;
        }
      });
      
      // Connect assert to exit
      edges.push(createEdge(assertNodeId, 'exit', ''));
    }
    
    // Always add exit node
    nodes.push(createNode('Exit', 'exit', 'Exit point'));
    
    return {
      nodes,
      edges,
      entryNode: 'entry',
      exitNode: 'exit'
    };
  } catch (error) {
    console.error('Error generating mock CFG:', error);
    
    // Return a minimal valid CFG
    return {
      nodes: [
        createNode('Entry', 'entry', 'Entry point'),
        createNode('Error generating CFG', 'error', 'Error'),
        createNode('Exit', 'exit', 'Exit point')
      ],
      edges: [
        createEdge('entry', 'error', ''),
        createEdge('error', 'exit', '')
      ],
      entryNode: 'entry',
      exitNode: 'exit'
    };
  }
};

/**
 * Helper function to create a CFG node
 */
function createNode(label: string, id: string, type: string): CFGNode {
  return {
    id,
    label,
    type,
    metadata: {
      lineNumber: 0
    }
  };
}

/**
 * Helper function to create a CFG edge
 */
function createEdge(source: string, target: string, label: string): CFGEdge {
  return {
    source,
    target,
    label,
    id: `${source}_to_${target}`
  };
}

/**
 * Node in a Control Flow Graph
 */
export interface CFGNode {
  id: string;
  label: string;
  type: string;
  metadata: {
    lineNumber: number;
    [key: string]: any;
  };
}

/**
 * Edge in a Control Flow Graph
 */
export interface CFGEdge {
  id: string;
  source: string;
  target: string;
  label: string;
} 