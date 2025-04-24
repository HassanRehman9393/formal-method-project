/**
 * Data Flow Analysis Framework
 * 
 * Provides a framework for forward and backward data flow analyses
 * that can be used by optimization passes
 */

/**
 * Directions for data flow analysis
 */
export const DataFlowDirection = {
  FORWARD: 'forward',
  BACKWARD: 'backward'
};

/**
 * Lattice join operations
 */
export const JoinOperation = {
  UNION: 'union',
  INTERSECTION: 'intersection'
};

/**
 * Base class for data flow analysis problems
 */
class DataFlowAnalysis {
  constructor(direction, joinOp) {
    this.direction = direction;
    this.joinOperation = joinOp;
  }
  
  /**
   * Get successor blocks for a given block
   * @param {SSAGraphNode} node - Block to get successors for
   * @param {SSAGraph} graph - The SSA graph
   * @returns {SSAGraphNode[]} List of successor nodes
   */
  getSuccessors(node, graph) {
    return node.successors.map(id => graph.nodes.get(id)).filter(Boolean);
  }
  
  /**
   * Get predecessor blocks for a given block
   * @param {SSAGraphNode} node - Block to get predecessors for
   * @param {SSAGraph} graph - The SSA graph
   * @returns {SSAGraphNode[]} List of predecessor nodes
   */
  getPredecessors(node, graph) {
    return node.predecessors.map(id => graph.nodes.get(id)).filter(Boolean);
  }
  
  /**
   * Get the appropriate adjacent nodes based on analysis direction
   * @param {SSAGraphNode} node - Current node
   * @param {SSAGraph} graph - SSA graph
   * @returns {SSAGraphNode[]} Adjacent nodes
   */
  getAdjacentNodes(node, graph) {
    return this.direction === DataFlowDirection.FORWARD ? 
      this.getSuccessors(node, graph) : 
      this.getPredecessors(node, graph);
  }
  
  /**
   * Initialize the data flow values for all nodes
   * @param {SSAGraph} graph - The SSA graph
   * @returns {Map} Map of block IDs to initial values
   */
  initialize(graph) {
    const values = new Map();
    for (const node of graph.getAllNodes()) {
      values.set(node.blockId, this.initialValue(node));
    }
    return values;
  }
  
  /**
   * Merge values based on the join operation
   * @param {Array} values - Values to merge
   * @returns {*} Merged value
   */
  merge(values) {
    if (!values || values.length === 0) return this.defaultValue();
    
    if (values.length === 1) return values[0];
    
    let result = values[0];
    for (let i = 1; i < values.length; i++) {
      result = this.join(result, values[i]);
    }
    
    return result;
  }
  
  /**
   * Run the data flow analysis on the given graph
   * @param {SSAGraph} graph - The SSA graph to analyze
   * @returns {Map} Map of block IDs to final values
   */
  analyze(graph) {
    if (!graph) throw new Error('No graph provided for analysis');
    
    let values = this.initialize(graph);
    let changed = true;
    const nodes = this.getProcessingOrder(graph);
    
    // Iterate until fixed point
    while (changed) {
      changed = false;
      
      for (const node of nodes) {
        // Get input values from predecessors/successors
        const adjacentNodes = this.getAdjacentNodes(node, graph);
        const inputValues = adjacentNodes.map(n => values.get(n.blockId)).filter(Boolean);
        
        // Merge input values
        const mergedValue = this.merge(inputValues);
        
        // Apply transfer function
        const oldValue = values.get(node.blockId);
        const newValue = this.transferFunction(node, mergedValue, graph);
        
        // Check if value changed
        if (!this.equals(oldValue, newValue)) {
          values.set(node.blockId, newValue);
          changed = true;
        }
      }
    }
    
    return values;
  }
  
  /**
   * Get the order in which nodes should be processed
   * @param {SSAGraph} graph - The SSA graph
   * @returns {SSAGraphNode[]} Ordered list of nodes to process
   */
  getProcessingOrder(graph) {
    if (this.direction === DataFlowDirection.FORWARD) {
      // Start from entry and follow successors
      return this.getTopologicalOrder(graph);
    } else {
      // Start from exits and follow predecessors
      return this.getTopologicalOrder(graph).reverse();
    }
  }
  
  /**
   * Get a topological ordering of the graph nodes
   * @param {SSAGraph} graph - The SSA graph
   * @returns {SSAGraphNode[]} Topologically ordered nodes
   */
  getTopologicalOrder(graph) {
    const visited = new Set();
    const order = [];
    
    function visit(nodeId) {
      if (visited.has(nodeId)) return;
      visited.add(nodeId);
      
      const node = graph.nodes.get(nodeId);
      if (!node) return;
      
      for (const succId of node.successors) {
        visit(succId);
      }
      
      order.unshift(node); // Add to front for topological order
    }
    
    // Start from entry
    if (graph.entryNode) {
      visit(graph.entryNode.blockId);
    }
    
    // Handle any disconnected nodes
    for (const node of graph.getAllNodes()) {
      if (!visited.has(node.blockId)) {
        visit(node.blockId);
      }
    }
    
    return order;
  }
  
  /**
   * Override these methods in subclasses:
   */
  
  /** 
   * Initial value for a node
   * @param {SSAGraphNode} node - The node to initialize
   * @returns {*} Initial value
   */
  initialValue(node) {
    return this.defaultValue();
  }
  
  /**
   * Default value for uninitialized nodes
   * @returns {*} Default value
   */
  defaultValue() {
    return null;
  }
  
  /**
   * Join two values based on the join operation
   * @param {*} val1 - First value
   * @param {*} val2 - Second value
   * @returns {*} Joined value
   */
  join(val1, val2) {
    return val1; // Default does nothing
  }
  
  /**
   * Apply the transfer function to a value
   * @param {SSAGraphNode} node - Current node
   * @param {*} value - Input value
   * @param {SSAGraph} graph - SSA graph
   * @returns {*} Output value
   */
  transferFunction(node, value, graph) {
    return value; // Default is identity function
  }
  
  /**
   * Check if two values are equal
   * @param {*} val1 - First value
   * @param {*} val2 - Second value
   * @returns {boolean} True if values are equal
   */
  equals(val1, val2) {
    return val1 === val2;
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

export { DataFlowAnalysis };
