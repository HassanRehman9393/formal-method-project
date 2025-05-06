/**
 * Data Flow Analysis Framework
 * 
 * A generic framework for performing data flow analysis on SSA programs
 */

/**
 * Enum for data flow direction
 */
export const DataFlowDirection = {
  FORWARD: 'forward',
  BACKWARD: 'backward'
};

/**
 * Enum for join operation types
 */
export const JoinOperation = {
  UNION: 'union',
  INTERSECTION: 'intersection',
  PRODUCT: 'product'
};

/**
 * Abstract base class for data flow analysis
 */
export class DataFlowAnalysis {
  /**
   * Create a new data flow analysis
   * @param {string} direction - Direction of analysis (forward or backward)
   * @param {string} joinOp - Type of join operation to use
   */
  constructor(direction = DataFlowDirection.FORWARD, joinOp = JoinOperation.UNION) {
    this.direction = direction;
    this.joinOp = joinOp;
    
    // Default values for worklist algorithm
    this.maxIterations = 100;
    this.debug = false;
  }
  
  /**
   * Initial value for the data flow domain
   * Override in subclasses
   */
  initialValue(node) {
    throw new Error('initialValue must be implemented by subclass');
  }
  
  /**
   * Default value for nodes
   * Override in subclasses
   */
  defaultValue() {
    throw new Error('defaultValue must be implemented by subclass');
  }
  
  /**
   * Join operation for combining values
   * Override in subclasses
   * @param {*} val1 - First value
   * @param {*} val2 - Second value
   * @returns {*} Joined value
   */
  join(val1, val2) {
    throw new Error('join must be implemented by subclass');
  }
  
  /**
   * Transfer function for a node
   * Override in subclasses
   * @param {object} node - Current node
   * @param {*} inValue - Input value
   * @param {object} graph - The SSA graph
   * @returns {*} Output value
   */
  transferFunction(node, inValue, graph) {
    throw new Error('transferFunction must be implemented by subclass');
  }
  
  /**
   * Check if two values are equal
   * Override in subclasses for custom equality checks
   * @param {*} val1 - First value
   * @param {*} val2 - Second value
   * @returns {boolean} True if equal
   */
  equals(val1, val2) {
    if (typeof val1 !== typeof val2) return false;
    
    // For primitive types
    if (typeof val1 !== 'object' || val1 === null) {
      return val1 === val2;
    }
    
    // For arrays
    if (Array.isArray(val1) && Array.isArray(val2)) {
      if (val1.length !== val2.length) return false;
      for (let i = 0; i < val1.length; i++) {
        if (!this.equals(val1[i], val2[i])) return false;
      }
      return true;
    }
    
    // For objects (default implementation)
    return JSON.stringify(val1) === JSON.stringify(val2);
  }
  
  /**
   * Run the data flow analysis on the SSA graph
   * @param {object} graph - The SSA graph
   * @returns {object} Analysis results
   */
  analyze(graph) {
    if (!graph || !graph.nodes || !graph.edges) {
      return { results: new Map(), iterations: 0, converged: false };
    }
    
    // Initialize result values for all nodes
    const results = new Map();
    for (const [nodeId, node] of graph.nodes) {
      results.set(nodeId, this.defaultValue());
    }
    
    // Set initial value for entry/exit node based on direction
    const startNodes = this.direction === DataFlowDirection.FORWARD ? 
      graph.getEntryNodes() : 
      graph.getExitNodes();
    
    for (const startNode of startNodes) {
      if (startNode && graph.nodes.has(startNode)) {
        results.set(startNode, this.initialValue(graph.nodes.get(startNode)));
      }
    }
    
    // Setup worklist
    let worklist = Array.from(graph.nodes.keys());
    let iterations = 0;
    let changed = true;
    
    // Continue until no changes or max iterations
    while (changed && iterations < this.maxIterations) {
      iterations++;
      changed = false;
      
      // Sort worklist based on direction (ensures proper traversal order)
      if (this.direction === DataFlowDirection.FORWARD) {
        // For forward analysis, process in topological order
        worklist = graph.getTopologicalOrder();
      } else {
        // For backward analysis, process in reverse topological order
        worklist = graph.getTopologicalOrder().reverse();
      }
      
      for (const nodeId of worklist) {
        const node = graph.nodes.get(nodeId);
        if (!node) continue;
        
        // Get input value based on predecessors/successors
        let inValue;
        
        if (this.direction === DataFlowDirection.FORWARD) {
          // Forward analysis: use values from predecessors
          const predecessors = graph.getPredecessors(nodeId);
          if (predecessors.length === 0) {
            // Entry node
            inValue = results.get(nodeId);
          } else {
            // Join values from all predecessors
            inValue = predecessors.reduce((acc, predId) => {
              const predValue = results.get(predId) || this.defaultValue();
              return acc === undefined ? predValue : this.join(acc, predValue);
            }, undefined);
          }
        } else {
          // Backward analysis: use values from successors
          const successors = graph.getSuccessors(nodeId);
          if (successors.length === 0) {
            // Exit node
            inValue = results.get(nodeId);
          } else {
            // Join values from all successors
            inValue = successors.reduce((acc, succId) => {
              const succValue = results.get(succId) || this.defaultValue();
              return acc === undefined ? succValue : this.join(acc, succValue);
            }, undefined);
          }
        }
        
        // Apply transfer function
        const oldValue = results.get(nodeId);
        const newValue = this.transferFunction(node, inValue, graph);
        
        // Check if value changed
        if (!this.equals(oldValue, newValue)) {
          results.set(nodeId, newValue);
          changed = true;
        }
      }
      
      if (this.debug) {
        console.log(`Iteration ${iterations}, changed: ${changed}`);
      }
    }
    
    return {
      results,
      iterations,
      converged: iterations < this.maxIterations
    };
  }
}

/**
 * Analyze data flow in an SSA program
 * @param {object} ssaProgram - SSA program to analyze
 * @param {object} analysis - Analysis instance to apply
 * @returns {object} Analysis results
 */
export function analyzeDataFlow(ssaProgram, analysis) {
  if (!ssaProgram) {
    throw new Error('No SSA program provided for analysis');
  }
  
  if (!analysis) {
    throw new Error('No analysis specified');
  }
  
  // Import dynamically to avoid circular dependencies
  const { buildSSAGraph } = require('./ssaGraph.js');
  
  // Build the SSA graph
  const graph = buildSSAGraph(ssaProgram);
  
  // Perform the analysis
  const results = analysis.analyze(graph);
  
  return {
    results,
    graph
  };
}

/**
 * Live Variables Analysis for dead code elimination
 */
export class LiveVariableAnalysis extends DataFlowAnalysis {
  constructor() {
    // Live variable analysis is a backward dataflow analysis
    super(DataFlowDirection.BACKWARD, JoinOperation.UNION);
  }
  
  /**
   * Initial value is an empty set (no variables live)
   */
  initialValue() {
    return new Set();
  }
  
  /**
   * Default value is an empty set
   */
  defaultValue() {
    return new Set();
  }
  
  /**
   * Union of two sets (join operation)
   */
  join(set1, set2) {
    const result = new Set(set1);
    for (const item of set2) {
      result.add(item);
    }
    return result;
  }
  
  /**
   * Transfer function: compute live variables before a block
   * based on variables used in the block and live after the block
   */
  transferFunction(node, outSet, graph) {
    // Start with the output set (variables live at exit)
    const result = new Set(outSet);
    
    // Process instructions in reverse order
    const instructions = [...node.instructions].reverse();
    
    // Process block terminator if present
    if (node.blockId && graph.nodes.has(node.blockId)) {
      const originalNode = graph.nodes.get(node.blockId);
      if (originalNode && originalNode.terminator) {
        // Add variables used in the terminator condition
        if (originalNode.terminator.condition) {
          const usedVars = this.getUsedVariables(originalNode.terminator.condition);
          for (const v of usedVars) {
            result.add(v);
          }
        }
      }
    }
    
    // Process instructions
    for (const instr of instructions) {
      if (!instr) continue;
      
      if (instr.type === 'Assignment') {
        // Remove the target (it's defined here)
        result.delete(instr.target);
        
        // Add variables used in the value
        const usedVars = this.getUsedVariables(instr.value);
        for (const v of usedVars) {
          result.add(v);
        }
      } else if (instr.type === 'Assert') {
        // Add variables used in the assertion
        const usedVars = this.getUsedVariables(instr.condition);
        for (const v of usedVars) {
          result.add(v);
        }
      }
    }
    
    // Process phi functions
    const phiFunctions = node.phiFunctions || [];
    for (const phi of phiFunctions) {
      if (!phi) continue;
      
      // Remove the target (it's defined here)
      result.delete(phi.target);
      
      // Add all source variables as they're used
      for (const source of phi.sources) {
        result.add(source);
      }
    }
    
    return result;
  }
  
  /**
   * Extract variables used in an expression
   * @param {object} expr - Expression to analyze
   * @returns {Set<string>} Set of variable names
   */
  getUsedVariables(expr) {
    const variables = new Set();
    
    if (!expr) return variables;
    
    const visitNode = (node) => {
      if (!node || typeof node !== 'object') return;
      
      // Check node type
      if (node.type === 'Variable') {
        variables.add(node.name);
        return;
      }
      
      // Recursively visit child nodes
      for (const key in node) {
        if (node[key] && typeof node[key] === 'object') {
          visitNode(node[key]);
        }
      }
    };
    
    visitNode(expr);
    return variables;
  }
  
  /**
   * Compare two sets for equality
   */
  equals(set1, set2) {
    if (set1.size !== set2.size) return false;
    for (const item of set1) {
      if (!set2.has(item)) return false;
    }
    return true;
  }
}

/**
 * Available Expressions Analysis for common subexpression elimination
 */
export class AvailableExpressionsAnalysis extends DataFlowAnalysis {
  constructor() {
    // Available expressions analysis is a forward dataflow analysis
    super(DataFlowDirection.FORWARD, JoinOperation.INTERSECTION);
  }
  
  /**
   * Initial value is an empty map
   */
  initialValue() {
    return new Map();
  }
  
  /**
   * Default value is an empty map
   */
  defaultValue() {
    return new Map();
  }
  
  /**
   * Intersection of two maps (join operation)
   */
  join(map1, map2) {
    const result = new Map();
    
    // Add elements that are in both maps
    for (const [key, value] of map1) {
      if (map2.has(key)) {
        result.set(key, value);
      }
    }
    
    return result;
  }
  
  /**
   * Transfer function: compute available expressions after a block
   * based on expressions killed and generated in the block
   */
  transferFunction(node, inMap, graph) {
    // Start with the input map (expressions available at entry)
    const result = new Map(inMap);
    
    // Process instructions
    for (const instr of node.instructions) {
      if (!instr) continue;
      
      if (instr.type === 'Assignment') {
        // Kill expressions that use the assigned variable
        const target = instr.target;
        if (target) {
          // Remove expressions that use this variable
          for (const [key, expr] of result) {
            if (this.expressionUsesVariable(expr, target)) {
              result.delete(key);
            }
          }
        }
        
        // Generate new expressions
        if (instr.value && instr.value.type === 'BinaryExpression') {
          const exprKey = this.expressionToKey(instr.value);
          if (exprKey) {
            result.set(exprKey, {
              expr: instr.value,
              var: instr.target
            });
          }
        }
      }
    }
    
    return result;
  }
  
  /**
   * Check if an expression uses a specific variable
   * @param {object} expr - The expression object
   * @param {string} variable - Variable name
   * @returns {boolean} True if the expression uses the variable
   */
  expressionUsesVariable(exprInfo, variable) {
    if (!exprInfo || !exprInfo.expr) return false;
    
    const expr = exprInfo.expr;
    
    // Check if left or right side uses the variable
    if (expr.left && expr.left.type === 'Variable' && expr.left.name === variable) {
      return true;
    }
    
    if (expr.right && expr.right.type === 'Variable' && expr.right.name === variable) {
      return true;
    }
    
    return false;
  }
  
  /**
   * Convert an expression to a unique string key
   * @param {object} expr - The expression to convert
   * @returns {string} A unique key for the expression
   */
  expressionToKey(expr) {
    if (!expr || expr.type !== 'BinaryExpression') return null;
    
    // For simplicity, use a string representation
    // In a production system, we'd use a more sophisticated approach
    return `${JSON.stringify(expr.left)}-${expr.operator}-${JSON.stringify(expr.right)}`;
  }
  
  /**
   * Compare two maps for equality
   */
  equals(map1, map2) {
    if (map1.size !== map2.size) return false;
    
    for (const [key, value] of map1) {
      if (!map2.has(key)) return false;
      
      // For simplicity, just compare keys
      // In a production system, we'd also compare values
    }
    
    return true;
  }
}
