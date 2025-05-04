/**
 * SSA Graph Builder
 * 
 * Creates a graph representation of SSA programs for analysis
 */

/**
 * SSA graph node representing a basic block
 */
class SSAGraphNode {
  constructor(blockId) {
    this.blockId = blockId;
    this.instructions = [];
    this.phiFunctions = [];
    this.predecessors = [];
    this.successors = [];
    this.dominator = null;
    this.dominanceFrontier = [];
  }

  /**
   * Add an instruction to this node
   * @param {object} instruction - The SSA instruction
   */
  addInstruction(instruction) {
    this.instructions.push(instruction);
  }

  /**
   * Add a phi function to this node
   * @param {object} phi - The phi function
   */
  addPhiFunction(phi) {
    this.phiFunctions.push(phi);
  }

  /**
   * Add a predecessor node
   * @param {string} blockId - ID of the predecessor block
   */
  addPredecessor(blockId) {
    if (!this.predecessors.includes(blockId)) {
      this.predecessors.push(blockId);
    }
  }

  /**
   * Add a successor node
   * @param {string} blockId - ID of the successor block
   */
  addSuccessor(blockId) {
    if (!this.successors.includes(blockId)) {
      this.successors.push(blockId);
    }
  }
}

/**
 * SSA Graph representing the program structure
 */
class SSAGraph {
  constructor() {
    this.nodes = new Map(); // Map of block ID to SSAGraphNode
    this.entryNode = null;
    this.exitNodes = [];
    this.variables = new Map(); // Variable definitions map
  }

  /**
   * Get or create a node for a block
   * @param {string} blockId - Block identifier
   * @returns {SSAGraphNode} The graph node
   */
  getOrCreateNode(blockId) {
    if (!this.nodes.has(blockId)) {
      this.nodes.set(blockId, new SSAGraphNode(blockId));
    }
    return this.nodes.get(blockId);
  }

  /**
   * Set the entry node
   * @param {string} blockId - Entry block ID
   */
  setEntryNode(blockId) {
    this.entryNode = this.getOrCreateNode(blockId);
  }

  /**
   * Add an exit node
   * @param {string} blockId - Exit block ID
   */
  addExitNode(blockId) {
    const node = this.getOrCreateNode(blockId);
    if (!this.exitNodes.includes(node)) {
      this.exitNodes.push(node);
    }
  }

  /**
   * Add an edge between two blocks
   * @param {string} fromId - Source block ID
   * @param {string} toId - Target block ID
   */
  addEdge(fromId, toId) {
    const fromNode = this.getOrCreateNode(fromId);
    const toNode = this.getOrCreateNode(toId);
    
    fromNode.addSuccessor(toId);
    toNode.addPredecessor(fromId);
  }

  /**
   * Record a variable definition
   * @param {string} variableName - SSA variable name
   * @param {object} definition - Definition information
   * @param {string} blockId - Block where variable is defined
   */
  addVariableDefinition(variableName, definition, blockId) {
    if (!this.variables.has(variableName)) {
      this.variables.set(variableName, []);
    }
    
    this.variables.get(variableName).push({
      def: definition,
      block: blockId
    });
  }

  /**
   * Get variable definition locations
   * @param {string} variableName - Variable name to find
   * @returns {Array} List of definition locations
   */
  getVariableDefinitions(variableName) {
    return this.variables.get(variableName) || [];
  }

  /**
   * Get all nodes in the graph
   * @returns {SSAGraphNode[]} Array of all nodes
   */
  getAllNodes() {
    return Array.from(this.nodes.values());
  }

  /**
   * Compute dominators for all nodes in the graph
   * This uses the iterative algorithm for finding dominators
   */
  computeDominators() {
    if (!this.entryNode) return;
    
    const nodes = this.getAllNodes();
    const n = nodes.length;
    
    // Initialize dominators
    for (const node of nodes) {
      node.dominators = new Set(nodes.map(n => n.blockId));
    }
    
    // Entry node only dominates itself
    this.entryNode.dominators = new Set([this.entryNode.blockId]);
    
    let changed = true;
    while (changed) {
      changed = false;
      
      for (const node of nodes) {
        if (node === this.entryNode) continue;
        
        // Start with universal set
        const newDominators = new Set(nodes.map(n => n.blockId));
        
        // Intersect with predecessors
        for (const predId of node.predecessors) {
          const pred = this.nodes.get(predId);
          if (!pred) continue;
          
          const intersection = new Set();
          for (const id of newDominators) {
            if (pred.dominators.has(id)) {
              intersection.add(id);
            }
          }
          
          newDominators.clear();
          for (const id of intersection) {
            newDominators.add(id);
          }
        }
        
        // Add self
        newDominators.add(node.blockId);
        
        // Check if changed
        if (newDominators.size !== node.dominators.size) {
          changed = true;
          node.dominators = newDominators;
        } else {
          for (const id of newDominators) {
            if (!node.dominators.has(id)) {
              changed = true;
              node.dominators = newDominators;
              break;
            }
          }
        }
      }
    }
    
    // Set immediate dominator
    for (const node of nodes) {
      if (node === this.entryNode) continue;
      
      const dominators = Array.from(node.dominators).filter(id => id !== node.blockId);
      if (dominators.length > 0) {
        // Find the closest dominator (the one that doesn't dominate other dominators)
        let immediateDominator = null;
        for (const domId of dominators) {
          let isImmediate = true;
          for (const otherId of dominators) {
            if (domId !== otherId) {
              const otherNode = this.nodes.get(otherId);
              if (otherNode && otherNode.dominators.has(domId)) {
                isImmediate = false;
                break;
              }
            }
          }
          if (isImmediate) {
            immediateDominator = domId;
            break;
          }
        }
        node.dominator = immediateDominator;
      }
    }
  }

  /**
   * Compute dominance frontiers for all nodes
   * Must be called after computeDominators
   */
  computeDominanceFrontiers() {
    for (const node of this.getAllNodes()) {
      node.dominanceFrontier = [];
    }
    
    for (const node of this.getAllNodes()) {
      // If node has multiple predecessors
      if (node.predecessors.length >= 2) {
        for (const predId of node.predecessors) {
          let runner = this.nodes.get(predId);
          if (!runner) continue;
          
          // Traverse up the dominator tree until we hit the immediate dominator of the current node
          while (runner && runner.blockId !== node.dominator) {
            runner.dominanceFrontier.push(node.blockId);
            runner = runner.dominator ? this.nodes.get(runner.dominator) : null;
          }
        }
      }
    }
  }
}

/**
 * Creates a graph representation from an SSA program
 * @param {object} ssaProgram - The SSA program
 * @returns {object} Graph representation
 */
export function buildSSAGraph(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
    return { nodes: new Map(), edges: new Map() };
  }
  
  const graph = {
    nodes: new Map(),
    edges: new Map(),
    
    /**
     * Get predecessors of a node
     * @param {string} nodeId - Node ID
     * @returns {Array} Predecessor node IDs
     */
    getPredecessors(nodeId) {
      const incoming = [];
      
      for (const [fromId, targets] of this.edges) {
        if (targets.includes(nodeId)) {
          incoming.push(fromId);
        }
      }
      
      return incoming;
    },
    
    /**
     * Get successors of a node
     * @param {string} nodeId - Node ID
     * @returns {Array} Successor node IDs
     */
    getSuccessors(nodeId) {
      return Array.from(this.edges.get(nodeId) || []);
    },
    
    /**
     * Get entry nodes (those with no predecessors)
     * @returns {Array} Entry node IDs
     */
    getEntryNodes() {
      const entryNodes = [];
      
      for (const [nodeId] of this.nodes) {
        if (this.getPredecessors(nodeId).length === 0) {
          entryNodes.push(nodeId);
        }
      }
      
      return entryNodes;
    },
    
    /**
     * Get exit nodes (those with no successors)
     * @returns {Array} Exit node IDs
     */
    getExitNodes() {
      const exitNodes = [];
      
      for (const [nodeId] of this.nodes) {
        if (this.getSuccessors(nodeId).length === 0) {
          exitNodes.push(nodeId);
        }
      }
      
      return exitNodes;
    },
    
    /**
     * Get a topological ordering of nodes
     * @returns {Array} Node IDs in topological order
     */
    getTopologicalOrder() {
      const visited = new Set();
      const result = [];
      
      function dfs(nodeId) {
        if (visited.has(nodeId)) return;
        visited.add(nodeId);
        
        const successors = graph.getSuccessors(nodeId);
        for (const succ of successors) {
          dfs(succ);
        }
        
        result.unshift(nodeId); // Add to front for correct ordering
      }
      
      // Start DFS from all entry nodes
      for (const entry of this.getEntryNodes()) {
        dfs(entry);
      }
      
      // Handle any disconnected components
      for (const [nodeId] of this.nodes) {
        if (!visited.has(nodeId)) {
          dfs(nodeId);
        }
      }
      
      return result;
    },
    
    /**
     * Calculate dominators for all nodes
     * @returns {Map} Map of node IDs to sets of dominator node IDs
     */
    calculateDominators() {
      const dom = new Map();
      const allNodes = Array.from(this.nodes.keys());
      const entries = this.getEntryNodes();
      
      if (entries.length === 0) return dom;
      const entry = entries[0];
      
      // Initialize dominators
      for (const node of allNodes) {
        dom.set(node, new Set(allNodes));
      }
      
      // Entry node is only dominated by itself
      dom.set(entry, new Set([entry]));
      
      // Iterative algorithm to find dominators
      let changed = true;
      while (changed) {
        changed = false;
        
        for (const node of allNodes) {
          if (node === entry) continue;
          
          const preds = this.getPredecessors(node);
          if (preds.length === 0) continue;
          
          // Start with all nodes
          const newDom = new Set(allNodes);
          
          // Intersect with predecessors' dominators
          for (const pred of preds) {
            const predDom = dom.get(pred);
            if (predDom) {
              // Intersection
              const intersection = new Set();
              for (const d of newDom) {
                if (predDom.has(d)) {
                  intersection.add(d);
                }
              }
              // Update newDom
              newDom.clear();
              for (const d of intersection) {
                newDom.add(d);
              }
            }
          }
          
          // Add the node itself
          newDom.add(node);
          
          // Check if changed
          const oldDom = dom.get(node);
          if (oldDom && (oldDom.size !== newDom.size || 
              !Array.from(newDom).every(d => oldDom.has(d)))) {
            dom.set(node, newDom);
            changed = true;
          }
        }
      }
      
      return dom;
    }
  };
  
  // Add nodes
  for (const block of ssaProgram.blocks) {
    if (!block || !block.label) continue;
    
    // Create a node that represents this block
    graph.nodes.set(block.label, {
      ...block,
      blockId: block.label,
      instructions: [...block.instructions],
      phiFunctions: block.phiFunctions || []
    });
    
    // Initialize edges list
    graph.edges.set(block.label, []);
  }
  
  // Add edges based on terminators
  for (const block of ssaProgram.blocks) {
    if (!block || !block.label || !block.terminator) continue;
    
    const sourceId = block.label;
    
    if (block.terminator.type === 'Jump') {
      const targetId = block.terminator.target;
      if (targetId && graph.nodes.has(targetId)) {
        const outEdges = graph.edges.get(sourceId) || [];
        outEdges.push(targetId);
        graph.edges.set(sourceId, outEdges);
      }
    } else if (block.terminator.type === 'Branch') {
      const thenTarget = block.terminator.thenTarget;
      const elseTarget = block.terminator.elseTarget;
      
      const outEdges = graph.edges.get(sourceId) || [];
      
      if (thenTarget && graph.nodes.has(thenTarget)) {
        outEdges.push(thenTarget);
      }
      
      if (elseTarget && graph.nodes.has(elseTarget)) {
        outEdges.push(elseTarget);
      }
      
      graph.edges.set(sourceId, outEdges);
    }
  }
  
  return graph;
}

/**
 * Visualize an SSA graph to dot format (GraphViz)
 * @param {SSAGraph} graph - The SSA graph to visualize
 * @returns {string} Dot format string
 */
export function ssaGraphToDot(graph) {
  let dot = 'digraph SSAGraph {\n';
  dot += '  rankdir=TB;\n';
  dot += '  node [shape=box];\n';
  
  // Add nodes
  for (const node of graph.getAllNodes()) {
    // Create node label with instructions
    let label = `${node.blockId}\\n`;
    
    // Add phi functions
    for (const phi of node.phiFunctions) {
      label += `${phi.target} = φ(${phi.sources.join(', ')})\\n`;
    }
    
    // Add instructions
    for (const instr of node.instructions) {
      if (instr.type === 'Assignment') {
        label += `${instr.target} = ...\\n`;
      } else if (instr.type === 'Comment') {
        label += `// ${instr.text}\\n`;
      }
    }
    
    dot += `  "${node.blockId}" [label="${label}"];\n`;
    
    // Add edges to successors
    for (const succId of node.successors) {
      dot += `  "${node.blockId}" -> "${succId}";\n`;
    }
  }
  
  dot += '}\n';
  return dot;
}
