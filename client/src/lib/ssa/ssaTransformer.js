/**
 * SSA Transformer Module
 * 
 * Transforms an AST into Static Single Assignment (SSA) form
 */

import { Block, PhiFunction, Variable, Assignment } from './ssaNodes.js';
import { extractControlFlow } from './cfgBuilder.js';

class SSATransformer {
  constructor(options = {}) {
    // Configuration options
    this.options = {
      // Whether to insert phi functions for all variables
      insertAllPhiFunctions: options.insertAllPhiFunctions || false,
      // Whether to perform simple constant propagation
      performConstantPropagation: options.performConstantPropagation !== false,
      ...options
    };

    // Variable counter for creating unique SSA variable names
    this.variableCounter = new Map();

    // Map of original variable names to current SSA versions
    this.currentVersions = new Map();

    // List of blocks in the SSA form
    this.blocks = [];
    
    // Current block being processed
    this.currentBlock = null;
    
    // Variables defined in each block
    this.blockDefinitions = new Map();
    
    // Map of variables used in each block
    this.blockUses = new Map();
  }

  /**
   * Reset the transformer state
   */
  reset() {
    this.variableCounter = new Map();
    this.currentVersions = new Map();
    this.blocks = [];
    this.currentBlock = null;
    this.blockDefinitions = new Map();
    this.blockUses = new Map();
  }

  /**
   * Generate a new SSA variable name with index
   * @param {string} name - Original variable name
   * @returns {string} SSA variable name (e.g., "x_3")
   */
  freshVariable(name) {
    // Get the current counter for this variable
    const counter = this.variableCounter.get(name) || 0;
    // Increment the counter
    this.variableCounter.set(name, counter + 1);
    // Return the SSA variable name
    return `${name}_${counter}`;
  }

  /**
   * Get the current version of a variable
   * @param {string} name - Original variable name
   * @returns {string} Current SSA variable name or null if not defined
   */
  getCurrentVersion(name) {
    return this.currentVersions.get(name);
  }

  /**
   * Set the current version of a variable
   * @param {string} name - Original variable name
   * @param {string} version - SSA variable name
   */
  setCurrentVersion(name, version) {
    this.currentVersions.set(name, version);
  }

  /**
   * Create a new block in the SSA form
   * @param {string} label - Block label
   * @returns {Block} The new block
   */
  createBlock(label) {
    const block = new Block(label);
    this.blocks.push(block);
    this.blockDefinitions.set(block, new Set());
    this.blockUses.set(block, new Set());
    return block;
  }

  /**
   * Transform an AST into SSA form
   * @param {object} ast - The AST to transform
   * @param {object} options - Transformation options
   * @returns {object} Transformed program in SSA form
   */
  transform(ast, options = {}) {
    try {
      this.reset();
      
      // Validate input AST
      if (!ast) {
        console.error('No AST provided to transform');
        return this.createEmptyProgram('No AST provided');
      }
      
      // Handle loop unrolling if requested
      let processedAst = ast;
      if (options.handleLoops !== false) {
        const unrollDepth = options.unrollDepth || 5;
        const unrollAll = options.unrollAll || false;
        
        console.log(`Unrolling loops with depth: ${unrollDepth}, unrollAll: ${unrollAll}`);
        
        // Import dynamically to avoid circular dependencies
        import('./loopHandler.js').then(({ unrollLoops }) => {
          processedAst = unrollLoops(ast, { 
            unrollDepth, 
            unrollAll 
          });
        }).catch(err => {
          console.error('Error loading loop handler:', err);
        });
      }
      
      // 1. Extract the control flow graph from the AST
      const cfg = extractControlFlow(processedAst);
      
      // 2. Create blocks for each node in the CFG
      if (cfg.nodes && cfg.nodes.length > 0) {
        for (const node of cfg.nodes) {
          if (node && node.label) {
            this.createBlock(node.label);
          }
        }
      }
      
      // Create entry block if none exists
      if (this.blocks.length === 0) {
        this.createBlock('entry');
      }
      
      // 3. Process each block to generate SSA instructions
      for (const block of this.blocks) {
        this.processBlock(block, cfg);
      }
      
      // 4. Insert phi functions at join points
      this.insertPhiFunctions(cfg);
      
      // 5. Rename variables according to SSA rules
      this.renameVariables(cfg);
      
      // 6. Return the SSA representation
      return this.generateSSAProgram();
    } catch (error) {
      console.error('Error during SSA transformation:', error);
      return this.createEmptyProgram(`Error: ${error.message}`);
    }
  }

  /**
   * Create an empty SSA program structure with error information
   * @param {string} errorMessage - The error message to include
   * @returns {object} A minimal valid program structure
   */
  createEmptyProgram(errorMessage) {
    const errorBlock = new Block('error');
    errorBlock.addInstruction({
      type: 'Comment',
      text: errorMessage || 'Unknown error during transformation'
    });
    
    return {
      type: 'SSAProgram',
      blocks: [errorBlock]
    };
  }

  /**
   * Process a block to generate SSA instructions
   * @param {Block} block - The block to process
   * @param {object} cfg - Control flow graph
   */
  processBlock(block, cfg) {
    if (!block || !cfg) return;
    
    const cfgNode = cfg.nodes.find(node => node && node.label === block.label);
    
    if (!cfgNode || !cfgNode.statements) {
      // If no statements found, add a placeholder comment
      block.addInstruction({
        type: 'Comment',
        text: 'No statements to process'
      });
      return;
    }
    
    // Set the current block
    this.currentBlock = block;
    
    // Process each statement in the block
    for (const stmt of cfgNode.statements) {
      if (stmt) {
        this.processStatement(stmt);
      }
    }
  }

  /**
   * Process an assignment statement and convert it to SSA form
   * @param {object} stmt - AST assignment statement node
   */
  processAssignment(stmt) {
    if (!stmt || stmt.type !== 'AssignmentStatement') return;
    
    // Process the right-hand side expression
    const rhs = this.processExpression(stmt.value);
    
    // Process target (left-hand side)
    if (stmt.target.type === 'Identifier') {
      // Simple variable assignment
      const varName = stmt.target.name;
      const ssaVarName = this.freshVariable(varName);
      
      // Create SSA assignment instruction
      const assignment = new Assignment(ssaVarName, rhs);
      this.currentBlock.addInstruction(assignment);
      
      // Record that this variable is defined in this block
      this.blockDefinitions.get(this.currentBlock).add(varName);
      
      // Update the current version of the variable
      this.setCurrentVersion(varName, ssaVarName);
    } else if (stmt.target.type === 'ArrayAccess') {
      // Array assignment is more complex - handle later
      // For now, just process it as a basic instruction
      const array = this.processExpression(stmt.target.array);
      const index = this.processExpression(stmt.target.index);
      
      // Create a special array assignment instruction
      const instruction = {
        type: 'ArrayAssignment',
        array,
        index,
        value: rhs
      };
      this.currentBlock.addInstruction(instruction);
    }
  }

  /**
   * Process an expression and convert it to SSA form
   * @param {object} expr - AST expression node
   * @returns {string|object} SSA expression
   */
  processExpression(expr) {
    if (!expr) return null;

    switch (expr.type) {
      case 'Identifier':
        // For identifiers, use the current SSA version
        const varName = expr.name;
        const currentVersion = this.getCurrentVersion(varName);
        
        if (currentVersion) {
          // Record that this variable is used in this block
          this.blockUses.get(this.currentBlock).add(varName);
          return currentVersion;
        }
        // If no current version exists, this is a use-before-def,
        // which indicates a potential error or external variable
        return `${varName}_undefined`;
        
      case 'IntegerLiteral':
      case 'BooleanLiteral':
        // Literals can be used directly
        return expr.value;
        
      case 'BinaryExpression':
        // Process both sides of the binary expression
        const left = this.processExpression(expr.left);
        const right = this.processExpression(expr.right);
        
        // Return a binary expression object
        return {
          type: 'BinaryExpression',
          operator: expr.operator,
          left,
          right
        };
        
      case 'UnaryExpression':
        // Process the expression operand
        const operand = this.processExpression(expr.expression);
        
        // Return a unary expression object
        return {
          type: 'UnaryExpression',
          operator: expr.operator,
          operand
        };
        
      case 'ArrayAccess':
        // Process array and index expressions
        const array = this.processExpression(expr.array);
        const index = this.processExpression(expr.index);
        
        // Return an array access object
        return {
          type: 'ArrayAccess',
          array,
          index
        };
        
      default:
        // For unsupported expression types, return placeholder
        return `<${expr.type}>`;
    }
  }

  /**
   * Process an if statement and convert it to SSA form
   * @param {object} stmt - AST if statement node
   */
  processIfStatement(stmt) {
    if (!stmt || stmt.type !== 'IfStatement') return;
    
    // Process the condition
    const condition = this.processExpression(stmt.condition);
    
    // Create blocks for then and else branches
    const thenBlock = this.createBlock(`${this.currentBlock.label}_then`);
    const elseBlock = stmt.alternate 
      ? this.createBlock(`${this.currentBlock.label}_else`) 
      : null;
    const joinBlock = this.createBlock(`${this.currentBlock.label}_join`);
    
    // Add branching instruction to current block
    this.currentBlock.addBranch(condition, thenBlock.label, elseBlock ? elseBlock.label : joinBlock.label);
    
    // Process the then branch
    const prevBlock = this.currentBlock;
    this.currentBlock = thenBlock;
    this.processStatement(stmt.consequent);
    // Add jump to join block if no explicit return/break
    if (!thenBlock.hasTerminator()) {
      thenBlock.addJump(joinBlock.label);
    }
    
    // Process the else branch if it exists
    if (elseBlock && stmt.alternate) {
      this.currentBlock = elseBlock;
      this.processStatement(stmt.alternate);
      // Add jump to join block if no explicit return/break
      if (!elseBlock.hasTerminator()) {
        elseBlock.addJump(joinBlock.label);
      }
    }
    
    // Continue processing from the join block
    this.currentBlock = joinBlock;
  }

  /**
   * Process an assert statement
   * @param {object} stmt - AST assert statement node
   */
  processAssertStatement(stmt) {
    if (!stmt || stmt.type !== 'AssertStatement') return;
    
    // Process the condition expression
    const condition = this.processExpression(stmt.condition);
    
    // Add assert instruction to current block
    this.currentBlock.addInstruction({
      type: 'Assert',
      condition
    });
  }

  /**
   * Process a while statement and convert it to SSA form
   * @param {object} stmt - AST while statement node
   */
  processWhileStatement(stmt) {
    if (!stmt || stmt.type !== 'WhileStatement') return;
    
    // Create blocks for loop header, body, and exit
    const headerLabel = `${this.currentBlock.label}_while_header`;
    const bodyLabel = `${this.currentBlock.label}_while_body`;
    const exitLabel = `${this.currentBlock.label}_while_exit`;
    
    const headerBlock = this.createBlock(headerLabel);
    const bodyBlock = this.createBlock(bodyLabel);
    const exitBlock = this.createBlock(exitLabel);
    
    // Add jump from current block to header
    this.currentBlock.addJump(headerLabel);
    
    // Process the loop header (condition evaluation)
    this.currentBlock = headerBlock;
    const condition = this.processExpression(stmt.condition);
    
    // Add branch from header to body or exit based on condition
    headerBlock.addBranch(condition, bodyLabel, exitLabel);
    
    // Process the loop body
    this.currentBlock = bodyBlock;
    this.processStatement(stmt.body);
    
    // Jump back to header after body
    if (!bodyBlock.hasTerminator()) {
      bodyBlock.addJump(headerLabel);
    }
    
    // Continue from exit block
    this.currentBlock = exitBlock;
  }

  /**
   * Process a for statement and convert it to SSA form
   * @param {object} stmt - AST for statement node
   */
  processForStatement(stmt) {
    if (!stmt || stmt.type !== 'ForStatement') return;
    
    // Process initialization if present
    if (stmt.init) {
      this.processStatement(stmt.init);
    }
    
    // Create blocks for loop header, body, update, and exit
    const headerLabel = `${this.currentBlock.label}_for_header`;
    const bodyLabel = `${this.currentBlock.label}_for_body`;
    const updateLabel = `${this.currentBlock.label}_for_update`;
    const exitLabel = `${this.currentBlock.label}_for_exit`;
    
    const headerBlock = this.createBlock(headerLabel);
    const bodyBlock = this.createBlock(bodyLabel);
    const updateBlock = this.createBlock(updateLabel);
    const exitBlock = this.createBlock(exitLabel);
    
    // Jump to header
    this.currentBlock.addJump(headerLabel);
    
    // Process condition in header block
    this.currentBlock = headerBlock;
    let condition = { type: 'BooleanLiteral', value: true }; // Default to true if no condition
    if (stmt.condition) {
      condition = this.processExpression(stmt.condition);
    }
    
    // Add branch from header to body or exit
    headerBlock.addBranch(condition, bodyLabel, exitLabel);
    
    // Process loop body
    this.currentBlock = bodyBlock;
    this.processStatement(stmt.body);
    
    // Jump to update block
    if (!bodyBlock.hasTerminator()) {
      bodyBlock.addJump(updateLabel);
    }
    
    // Process update expression
    this.currentBlock = updateBlock;
    if (stmt.update) {
      this.processStatement(stmt.update);
    }
    
    // Jump back to header
    updateBlock.addJump(headerLabel);
    
    // Continue from exit block
    this.currentBlock = exitBlock;
  }

  /**
   * Insert phi functions at join points
   * @param {object} cfg - Control flow graph
   */
  insertPhiFunctions(cfg) {
    // For each block that has multiple predecessors (join point)
    for (const block of this.blocks) {
      const cfgNode = cfg.nodes.find(node => node.label === block.label);
      
      if (!cfgNode || cfgNode.predecessors.length <= 1) continue;
      
      // For each variable that may need a phi function
      const phiVariables = this.determinePhiVariables(block, cfgNode);
      
      // Insert phi functions at the beginning of the block
      for (const varName of phiVariables) {
        const phiFunction = new PhiFunction(varName, this.freshVariable(varName), cfgNode.predecessors);
        block.insertPhiFunction(phiFunction);
      }
    }
  }

  /**
   * Determine which variables need phi functions in a block
   * @param {Block} block - The block to analyze
   * @param {object} cfgNode - Corresponding CFG node
   * @returns {Set<string>} Set of variable names needing phi functions
   */
  determinePhiVariables(block, cfgNode) {
    const phiVariables = new Set();
    
    if (this.options.insertAllPhiFunctions) {
      // Conservative approach: insert phi functions for all variables
      // defined in any predecessor block
      for (const predLabel of cfgNode.predecessors) {
        const predBlock = this.blocks.find(b => b.label === predLabel);
        if (predBlock) {
          const definitions = this.blockDefinitions.get(predBlock);
          if (definitions) {
            for (const varName of definitions) {
              phiVariables.add(varName);
            }
          }
        }
      }
    } else {
      // Smarter approach: only insert phi functions for variables that
      // have different definitions reaching this join point
      // (This is a simplified version of the algorithm - a full implementation
      // would need to compute reaching definitions more accurately)
      
      // Get variables used in this block
      const usedVars = this.blockUses.get(block) || new Set();
      
      // For each variable used in this block
      for (const varName of usedVars) {
        let needsPhi = false;
        let seenDefinition = false;
        
        // Check if this variable is defined differently in predecessors
        for (const predLabel of cfgNode.predecessors) {
          const predBlock = this.blocks.find(b => b.label === predLabel);
          if (predBlock && this.blockDefinitions.get(predBlock).has(varName)) {
            if (seenDefinition) {
              needsPhi = true;
              break;
            }
            seenDefinition = true;
          }
        }
        
        if (needsPhi) {
          phiVariables.add(varName);
        }
      }
    }
    
    return phiVariables;
  }

  /**
   * Rename variables according to SSA rules
   * This is a simplified implementation that doesn't fully cover all edge cases
   * @param {object} cfg - Control flow graph
   */
  renameVariables(cfg) {
    // For now, we've been renaming variables as we go
    // A full implementation would do a more thorough job here
    // by traversing the CFG in a specific order
  }

  /**
   * Generate the final SSA program representation
   * @returns {object} Program in SSA form
   */
  generateSSAProgram() {
    // If no blocks were created, create a default empty block
    if (!this.blocks || this.blocks.length === 0) {
      this.createBlock('default');
    }
    
    return {
      type: 'SSAProgram',
      blocks: this.blocks.filter(Boolean) // Remove any null/undefined blocks
    };
  }

  /**
   * Format the SSA program as readable code
   * @param {object} ssaProgram - SSA program object
   * @returns {string} Formatted SSA code
   */
  formatSSACode(ssaProgram = null) {
    try {
      const program = ssaProgram || this.generateSSAProgram();
      let code = '';
      
      // Check if program and program.blocks exist
      if (!program || !program.blocks) {
        return '// Error: Invalid SSA program structure\n';
      }
      
      for (const block of program.blocks) {
        // Add null check for block
        if (!block) continue;
        
        // Add block label
        code += `${block.label}:\n`;
        
        // Add phi functions with null checks
        if (Array.isArray(block.phiFunctions)) {
          for (const phi of block.phiFunctions) {
            if (!phi) continue;
            try {
              const sources = Array.isArray(phi.sources) ? 
                phi.sources.map(src => `${phi.variable}_${src}`).join(', ') : '';
              code += `  ${phi.target} = φ(${sources})\n`;
            } catch (e) {
              code += `  // Error in phi function: ${e.message}\n`;
            }
          }
        }
        
        // Add instructions with null checks
        if (Array.isArray(block.instructions)) {
          for (const instr of block.instructions) {
            if (!instr) continue;
            
            try {
              if (instr.type === 'Comment') {
                code += `  // ${instr.text}\n`;
                continue;
              }
              
              if (instr.constructor && instr.constructor.name === 'Assignment') {
                code += `  ${instr.target} = ${this.formatExpression(instr.value)}\n`;
              } else if (instr.type === 'Assert') {
                code += `  assert(${this.formatExpression(instr.condition)})\n`;
              } else if (instr.type === 'ArrayAssignment') {
                code += `  ${this.formatExpression(instr.array)}[${this.formatExpression(instr.index)}] = ${this.formatExpression(instr.value)}\n`;
              } else {
                code += `  // Unknown instruction: ${JSON.stringify(instr)}\n`;
              }
            } catch (e) {
              code += `  // Error formatting instruction: ${e.message}\n`;
            }
          }
        }
        
        // Add terminator with null check
        if (block.terminator) {
          try {
            if (block.terminator.type === 'Jump') {
              code += `  goto ${block.terminator.target}\n`;
            } else if (block.terminator.type === 'Branch') {
              code += `  if (${this.formatExpression(block.terminator.condition)}) goto ${block.terminator.thenTarget} else goto ${block.terminator.elseTarget}\n`;
            } else if (block.terminator.type === 'Return') {
              code += `  return ${this.formatExpression(block.terminator.value)}\n`;
            }
          } catch (e) {
            code += `  // Error in terminator: ${e.message}\n`;
          }
        }
        
        code += '\n';
      }
      
      return code;
    } catch (error) {
      console.error('Error formatting SSA code:', error);
      return `// Error formatting SSA code: ${error.message}\n`;
    }
  }

  /**
   * Format an expression as readable code
   * @param {*} expr - Expression to format
   * @returns {string} Formatted expression
   */
  formatExpression(expr) {
    if (expr === null || expr === undefined) {
      return 'undefined';
    }
    
    if (typeof expr === 'string' || typeof expr === 'number' || typeof expr === 'boolean') {
      return String(expr);
    }
    
    // Add null check before accessing expr.type
    if (!expr || typeof expr !== 'object') {
      return 'invalid_expression';
    }
    
    try {
      switch (expr.type) {
        case 'BinaryExpression':
          return `${this.formatExpression(expr.left)} ${expr.operator} ${this.formatExpression(expr.right)}`;
          
        case 'UnaryExpression':
          return `${expr.operator}${this.formatExpression(expr.operand)}`;
          
        case 'ArrayAccess':
          return `${this.formatExpression(expr.array)}[${this.formatExpression(expr.index)}]`;
          
        default:
          return `<${expr.type || 'unknown'}>`;
      }
    } catch (error) {
      console.error('Error formatting expression:', error, expr);
      return 'error_expression';
    }
  }

  /**
   * Process a statement and convert it to SSA form
   * @param {object} stmt - AST statement node
   */
  processStatement(stmt) {
    if (!stmt) return;
    
    switch (stmt.type) {
      case 'AssignmentStatement':
        this.processAssignment(stmt);
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
        
      case 'BlockStatement':
        if (stmt.body && Array.isArray(stmt.body)) {
          for (const s of stmt.body) {
            this.processStatement(s);
          }
        }
        break;
        
      case 'AssertStatement':
        this.processAssertStatement(stmt);
        break;
        
      case 'Comment':
        // Handle comment nodes
        this.currentBlock.addInstruction({
          type: 'Comment',
          text: stmt.text
        });
        break;
        
      default:
        // For special comment instructions disguised as assignments
        if (stmt.type === 'AssignmentStatement' && 
            stmt.target?.type === 'Identifier' && 
            stmt.target.name.startsWith('/*')) {
          
          // Extract the comment text from the identifier name
          const commentText = stmt.target.name.replace(/\/\*|\*\//g, '').trim();
          this.currentBlock.addInstruction({
            type: 'Comment',
            text: commentText
          });
          return;
        }
        
        // For unsupported statement types, add a comment
        this.currentBlock.addInstruction({
          type: 'Comment',
          text: `Unhandled statement type: ${stmt.type}`
        });
    }
  }
}

export default SSATransformer;
