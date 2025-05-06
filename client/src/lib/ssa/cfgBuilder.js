/**
 * Control Flow Graph Builder
 * 
 * Extracts a control flow graph from an AST
 */

/**
 * Represents a node in the control flow graph
 */
class CFGNode {
  constructor(label) {
    this.label = label;
    this.statements = [];
    this.successors = [];
    this.predecessors = [];
  }

  addStatement(statement) {
    this.statements.push(statement);
  }

  addSuccessor(nodeLabel) {
    if (!this.successors.includes(nodeLabel)) {
      this.successors.push(nodeLabel);
    }
  }

  addPredecessor(nodeLabel) {
    if (!this.predecessors.includes(nodeLabel)) {
      this.predecessors.push(nodeLabel);
    }
  }
}

/**
 * Control flow graph
 */
class CFG {
  constructor() {
    this.nodes = [];
    this.entryNode = null;
    this.exitNode = null;
    this.nextNodeId = 0;
  }

  createNode(label = null) {
    const nodeLabel = label || `node_${this.nextNodeId++}`;
    const node = new CFGNode(nodeLabel);
    this.nodes.push(node);
    return node;
  }

  /**
   * Get a node by its label
   * @param {string} label - Node label
   * @returns {CFGNode|null} Found node or null
   */
  getNode(label) {
    return this.nodes.find(node => node.label === label) || null;
  }

  /**
   * Add an edge between two nodes
   * @param {string} fromLabel - Source node label
   * @param {string} toLabel - Target node label
   */
  addEdge(fromLabel, toLabel) {
    const fromNode = this.getNode(fromLabel);
    const toNode = this.getNode(toLabel);

    if (fromNode && toNode) {
      fromNode.addSuccessor(toLabel);
      toNode.addPredecessor(fromLabel);
    }
  }

  /**
   * Set the entry node of the CFG
   * @param {string} label - Entry node label
   */
  setEntryNode(label) {
    this.entryNode = this.getNode(label);
  }

  /**
   * Set the exit node of the CFG
   * @param {string} label - Exit node label
   */
  setExitNode(label) {
    this.exitNode = this.getNode(label);
  }
}

/**
 * CFG Builder class
 */
class CFGBuilder {
  constructor() {
    this.cfg = new CFG();
    this.currentNode = null;
    this.nextBlockId = 0;
  }

  /**
   * Generate a unique block label
   * @param {string} prefix - Label prefix
   * @returns {string} Unique block label
   */
  generateBlockLabel(prefix = 'block') {
    return `${prefix}_${this.nextBlockId++}`;
  }

  /**
   * Build a CFG from an AST
   * @param {object} ast - The AST to process
   * @returns {CFG} The constructed control flow graph
   */
  buildCFG(ast) {
    try {
      // Reset state
      this.cfg = new CFG();
      this.currentNode = null;
      this.nextBlockId = 0;

      // Check if we have a valid AST
      if (!ast) {
        console.warn('No AST provided to CFG builder');
        // Create a minimal valid CFG with just an entry and exit node
        const entryLabel = this.generateBlockLabel('entry');
        const exitLabel = this.generateBlockLabel('exit');
        
        this.currentNode = this.cfg.createNode(entryLabel);
        const exitNode = this.cfg.createNode(exitLabel);
        
        this.cfg.addEdge(entryLabel, exitLabel);
        this.cfg.setEntryNode(entryLabel);
        this.cfg.setExitNode(exitLabel);
        
        return this.cfg;
      }

      // Create entry node
      const entryLabel = this.generateBlockLabel('entry');
      this.currentNode = this.cfg.createNode(entryLabel);
      this.cfg.setEntryNode(entryLabel);

      // Process the AST
      if (ast.type === 'Program' && ast.statements) {
        this.processStatements(ast.statements);
      } else if (ast.type === 'Program' && ast.body) {
        this.processStatements(ast.body);
      } else if (Array.isArray(ast)) {
        this.processStatements(ast);
      } else {
        console.warn(`Unexpected AST structure with type: ${ast.type || 'unknown'}`);
        this.currentNode.addStatement({
          type: 'Comment',
          text: `Unexpected AST structure: ${JSON.stringify(ast).substring(0, 100)}...`
        });
      }

      // Create exit node if not already present
      if (!this.cfg.exitNode) {
        const exitLabel = this.generateBlockLabel('exit');
        const exitNode = this.cfg.createNode(exitLabel);
        this.cfg.addEdge(this.currentNode.label, exitLabel);
        this.cfg.setExitNode(exitLabel);
      }

      return this.cfg;
    } catch (error) {
      console.error('Error building CFG:', error);
      
      // Return minimal valid CFG
      const cfg = new CFG();
      const entryLabel = 'error_entry';
      const exitLabel = 'error_exit';
      
      const entryNode = cfg.createNode(entryLabel);
      const exitNode = cfg.createNode(exitLabel);
      
      entryNode.addStatement({
        type: 'Comment',
        text: `Error building CFG: ${error.message}`
      });
      
      cfg.addEdge(entryLabel, exitLabel);
      cfg.setEntryNode(entryLabel);
      cfg.setExitNode(exitLabel);
      
      return cfg;
    }
  }

  /**
   * Process a list of statements
   * @param {Array} statements - List of statement AST nodes
   */
  processStatements(statements) {
    if (!statements) {
      console.warn('No statements provided');
      return;
    }
    
    if (!Array.isArray(statements)) {
      console.warn('Non-array statements provided');
      // Try to process as a single statement if possible
      if (statements.type) {
        this.processStatement(statements);
      }
      return;
    }
  
    for (const stmt of statements) {
      if (stmt) {
        this.processStatement(stmt);
      }
    }
  }

  /**
   * Process a single statement
   * @param {object} stmt - Statement AST node
   */
  processStatement(stmt) {
    if (!stmt) return;

    switch (stmt.type) {
      case 'AssignmentStatement':
      case 'EmptyStatement':
      case 'AssertStatement':
        // Basic statements go into the current block
        this.currentNode.addStatement(stmt);
        break;

      case 'BlockStatement':
        // Process each statement in the block
        this.processStatements(stmt.body || []);
        break;

      case 'IfStatement':
        this.processIfStatement(stmt);
        break;

      case 'WhileStatement':
        this.processWhileStatement(stmt);
        break;

      case 'ForStatement':
        this.processForStatement(stmt);
        break;
        
      case 'Comment':
        // Handle comment statements
        this.currentNode.addStatement(stmt);
        break;

      default:
        console.warn(`Unhandled statement type in CFG builder: ${stmt.type}`);
        // Add as-is to current block as a fallback
        this.currentNode.addStatement({
          type: 'Comment',
          text: `Unhandled statement type: ${stmt.type}`
        });
    }
  }

  /**
   * Process an if statement
   * @param {object} stmt - If statement AST node
   */
  processIfStatement(stmt) {
    const currentLabel = this.currentNode.label;
    
    // Add the condition to the current block
    this.currentNode.addStatement({
      type: 'Condition',
      expression: stmt.condition
    });

    // Create then block
    const thenLabel = this.generateBlockLabel('then');
    const thenNode = this.cfg.createNode(thenLabel);
    this.cfg.addEdge(currentLabel, thenLabel);

    // Create merge block
    const mergeLabel = this.generateBlockLabel('merge');
    const mergeNode = this.cfg.createNode(mergeLabel);

    // Process then branch
    this.currentNode = thenNode;
    this.processStatement(stmt.consequent);
    this.cfg.addEdge(this.currentNode.label, mergeLabel);

    // Process else branch if it exists
    if (stmt.alternate) {
      const elseLabel = this.generateBlockLabel('else');
      const elseNode = this.cfg.createNode(elseLabel);
      this.cfg.addEdge(currentLabel, elseLabel);

      this.currentNode = elseNode;
      this.processStatement(stmt.alternate);
      this.cfg.addEdge(this.currentNode.label, mergeLabel);
    } else {
      // If no else branch, create direct edge from condition to merge
      this.cfg.addEdge(currentLabel, mergeLabel);
    }

    // Continue from the merge point
    this.currentNode = mergeNode;
  }

  /**
   * Process a while statement
   * @param {object} stmt - While statement AST node
   */
  processWhileStatement(stmt) {
    // Create header block for the loop condition
    const headerLabel = this.generateBlockLabel('while_header');
    const headerNode = this.cfg.createNode(headerLabel);
    this.cfg.addEdge(this.currentNode.label, headerLabel);

    // Create body block
    const bodyLabel = this.generateBlockLabel('while_body');
    const bodyNode = this.cfg.createNode(bodyLabel);

    // Create exit block
    const exitLabel = this.generateBlockLabel('while_exit');
    const exitNode = this.cfg.createNode(exitLabel);

    // Add condition to header block
    headerNode.addStatement({
      type: 'Condition',
      expression: stmt.condition
    });

    // Add edges from header to body and exit
    this.cfg.addEdge(headerLabel, bodyLabel); // True edge
    this.cfg.addEdge(headerLabel, exitLabel); // False edge

    // Process loop body
    this.currentNode = bodyNode;
    this.processStatement(stmt.body);
    this.cfg.addEdge(this.currentNode.label, headerLabel); // Back edge

    // Continue from exit block
    this.currentNode = exitNode;
  }

  /**
   * Process a for statement
   * @param {object} stmt - For statement AST node
   */
  processForStatement(stmt) {
    // Process initialization if present
    if (stmt.init) {
      this.currentNode.addStatement(stmt.init);
    }

    // Create header block for the loop condition
    const headerLabel = this.generateBlockLabel('for_header');
    const headerNode = this.cfg.createNode(headerLabel);
    this.cfg.addEdge(this.currentNode.label, headerLabel);

    // Create body block
    const bodyLabel = this.generateBlockLabel('for_body');
    const bodyNode = this.cfg.createNode(bodyLabel);

    // Create update block
    const updateLabel = this.generateBlockLabel('for_update');
    const updateNode = this.cfg.createNode(updateLabel);

    // Create exit block
    const exitLabel = this.generateBlockLabel('for_exit');
    const exitNode = this.cfg.createNode(exitLabel);

    // Add condition to header block if present
    if (stmt.condition) {
      headerNode.addStatement({
        type: 'Condition',
        expression: stmt.condition
      });
      this.cfg.addEdge(headerLabel, bodyLabel); // True edge
      this.cfg.addEdge(headerLabel, exitLabel); // False edge
    } else {
      // If no condition, always enter the loop
      this.cfg.addEdge(headerLabel, bodyLabel);
    }

    // Process loop body
    this.currentNode = bodyNode;
    this.processStatement(stmt.body);
    this.cfg.addEdge(this.currentNode.label, updateLabel);

    // Process update if present
    if (stmt.update) {
      updateNode.addStatement(stmt.update);
    }
    this.cfg.addEdge(updateLabel, headerLabel); // Back edge

    // Continue from exit block
    this.currentNode = exitNode;
  }
}

/**
 * Convenience function to build a CFG from an AST
 * @param {object} ast - The AST to process
 * @returns {CFG} The constructed control flow graph
 */
export function buildCFG(ast) {
  const builder = new CFGBuilder();
  return builder.buildCFG(ast);
}

export { CFG, CFGNode, CFGBuilder };
