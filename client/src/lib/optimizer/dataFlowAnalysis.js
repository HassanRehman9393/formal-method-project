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
  CUSTOM: 'custom'
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
