/**
 * SMT Generator Service
 * Converts program constructs to SMT-LIB format constraints
 */

class SMTGenerator {
  constructor() {
    this.declarations = [];
    this.assertions = [];
    this.variables = new Set();
    this.nextVarId = 0;
    this.currentScope = 'global';
    this.scopes = ['global'];
  }

  /**
   * Reset the generator state
   */
  reset() {
    this.declarations = [];
    this.assertions = [];
    this.variables = new Set();
    this.nextVarId = 0;
    this.currentScope = 'global';
    this.scopes = ['global'];
  }

  /**
   * Generate SMT-LIB format constraints from program representation
   * @param {Object} ast - AST of the program
   * @returns {string} SMT-LIB format constraints
   */
  generateSMT(ast) {
    this.reset();
    
    // Process AST nodes and gather declarations and assertions
    if (ast && ast.type === 'Program') {
      this.processStatements(ast.body);
    } else if (ast && Array.isArray(ast)) {
      this.processStatements(ast);
    } else {
      throw new Error('Invalid AST structure');
    }
    
    // Generate the full SMT-LIB script
    return this.generateSMTScript();
  }

  /**
   * Process a list of statements
   * @param {Array} statements - List of statement AST nodes
   */
  processStatements(statements) {
    if (!statements || !Array.isArray(statements)) return;
    
    for (const statement of statements) {
      this.processNode(statement);
    }
  }

  /**
   * Process an AST node and generate corresponding SMT constraints
   * @param {Object} node - AST node
   * @returns {Object|null} SMT expression object or null
   */
  processNode(node) {
    if (!node) return null;
    
    switch (node.type) {
      case 'VariableDeclaration':
        return this.processVariableDeclaration(node);
      
      case 'AssignmentStatement':
        return this.processAssignment(node);
      
      case 'BinaryExpression':
        return this.processBinaryExpression(node);
      
      case 'UnaryExpression':
        return this.processUnaryExpression(node);
        
      case 'Identifier':
        return this.processIdentifier(node);
        
      case 'Literal':
        return this.processLiteral(node);
        
      case 'IfStatement':
        return this.processIfStatement(node);
        
      case 'WhileStatement':
        return this.processWhileStatement(node);
        
      case 'ForStatement':
        return this.processForStatement(node);
        
      case 'BlockStatement':
        return this.processBlockStatement(node);
        
      case 'AssertStatement':
        return this.processAssertStatement(node);
        
      case 'ArrayExpression':
        return this.processArrayExpression(node);
        
      case 'ArrayAccessExpression':
        return this.processArrayAccess(node);
        
      default:
        console.warn(`Unhandled node type: ${node.type}`);
        return null;
    }
  }

  /**
   * Process variable declaration
   * @param {Object} node - Variable declaration AST node
   * @returns {Object} SMT declaration
   */
  processVariableDeclaration(node) {
    const varName = node.id.name;
    const smtVarName = this.getSMTVarName(varName);
    
    // Register the variable
    this.variables.add(varName);
    
    // Generate declaration
    const declaration = `(declare-const ${smtVarName} Int)`;
    this.declarations.push(declaration);
    
    // If there's an initializer, generate an assertion for the initialization
    if (node.init) {
      const initValue = this.processNode(node.init);
      if (initValue) {
        const assertion = `(assert (= ${smtVarName} ${initValue}))`;
        this.assertions.push(assertion);
      }
    }
    
    return smtVarName;
  }

  /**
   * Process assignment statement
   * @param {Object} node - Assignment AST node
   * @returns {Object} SMT assertion
   */
  processAssignment(node) {
    const target = this.processNode(node.left);
    const value = this.processNode(node.right);
    
    if (target && value) {
      const assertion = `(assert (= ${target} ${value}))`;
      this.assertions.push(assertion);
      return value;
    }
    
    return null;
  }

  /**
   * Process binary expression
   * @param {Object} node - Binary expression AST node
   * @returns {string} SMT expression
   */
  processBinaryExpression(node) {
    const left = this.processNode(node.left);
    const right = this.processNode(node.right);
    
    if (!left || !right) return null;
    
    switch (node.operator) {
      // Arithmetic operators
      case '+': return `(+ ${left} ${right})`;
      case '-': return `(- ${left} ${right})`;
      case '*': return `(* ${left} ${right})`;
      case '/': return `(div ${left} ${right})`;
      case '%': return `(mod ${left} ${right})`;
      
      // Comparison operators
      case '==': return `(= ${left} ${right})`;
      case '!=': return `(not (= ${left} ${right}))`;
      case '<': return `(< ${left} ${right})`;
      case '<=': return `(<= ${left} ${right})`;
      case '>': return `(> ${left} ${right})`;
      case '>=': return `(>= ${left} ${right})`;
      
      // Logical operators
      case '&&': return `(and ${left} ${right})`;
      case '||': return `(or ${left} ${right})`;
      
      default:
        console.warn(`Unsupported binary operator: ${node.operator}`);
        return null;
    }
  }

  /**
   * Process unary expression
   * @param {Object} node - Unary expression AST node
   * @returns {string} SMT expression
   */
  processUnaryExpression(node) {
    const argument = this.processNode(node.argument);
    
    if (!argument) return null;
    
    switch (node.operator) {
      case '-': return `(- ${argument})`;
      case '!': return `(not ${argument})`;
      case '+': return argument; // Unary plus doesn't change the value
      
      default:
        console.warn(`Unsupported unary operator: ${node.operator}`);
        return null;
    }
  }

  /**
   * Process identifier
   * @param {Object} node - Identifier AST node
   * @returns {string} SMT variable name
   */
  processIdentifier(node) {
    const varName = node.name;
    return this.getSMTVarName(varName);
  }

  /**
   * Process literal
   * @param {Object} node - Literal AST node
   * @returns {string} SMT literal value
   */
  processLiteral(node) {
    if (typeof node.value === 'number') {
      return node.value.toString();
    } else if (typeof node.value === 'boolean') {
      return node.value ? 'true' : 'false';
    } else if (typeof node.value === 'string') {
      // String literals aren't directly supported in SMT-LIB for arithmetic
      console.warn('String literals are not supported in SMT constraints');
      return null;
    } else {
      return null;
    }
  }

  /**
   * Process if statement
   * @param {Object} node - If statement AST node
   */
  processIfStatement(node) {
    // For basic SMT generation, we'll simplify by just processing the condition,
    // consequence, and alternative separately without full path constraints
    const condition = this.processNode(node.test);
    
    if (condition) {
      // Process the consequence branch
      if (node.consequent) {
        this.enterScope('if_true');
        this.processNode(node.consequent);
        this.exitScope();
      }
      
      // Process the alternative branch
      if (node.alternate) {
        this.enterScope('if_false');
        this.processNode(node.alternate);
        this.exitScope();
      }
    }
    
    return null;
  }

  /**
   * Process assert statement
   * @param {Object} node - Assert statement AST node
   */
  processAssertStatement(node) {
    const condition = this.processNode(node.expression);
    
    if (condition) {
      const assertion = `(assert ${condition})`;
      this.assertions.push(assertion);
    }
    
    return null;
  }

  /**
   * Process block statement
   * @param {Object} node - Block statement AST node
   */
  processBlockStatement(node) {
    if (node.body && Array.isArray(node.body)) {
      this.processStatements(node.body);
    }
    return null;
  }

  /**
   * Process while statement (basic unrolling is not implemented here)
   * @param {Object} node - While statement AST node
   */
  processWhileStatement(node) {
    // For basic implementation, we don't fully handle loops
    // This would require loop unrolling which is planned for later phases
    console.warn('While statements require loop unrolling which is not fully implemented yet');
    return null;
  }

  /**
   * Process for statement (basic unrolling is not implemented here)
   * @param {Object} node - For statement AST node
   */
  processForStatement(node) {
    // For basic implementation, we don't fully handle loops
    // This would require loop unrolling which is planned for later phases
    console.warn('For statements require loop unrolling which is not fully implemented yet');
    return null;
  }

  /**
   * Process array expression
   * @param {Object} node - Array expression AST node
   */
  processArrayExpression(node) {
    // Basic array support isn't implemented in this phase
    console.warn('Array expressions are not fully supported yet');
    return null;
  }

  /**
   * Process array access
   * @param {Object} node - Array access AST node
   */
  processArrayAccess(node) {
    // Basic array support isn't implemented in this phase
    console.warn('Array access expressions are not fully supported yet');
    return null;
  }

  /**
   * Enter a new scope
   * @param {string} scopeName - Name of the new scope
   */
  enterScope(scopeName) {
    const newScope = `${this.currentScope}_${scopeName}`;
    this.scopes.push(newScope);
    this.currentScope = newScope;
  }

  /**
   * Exit the current scope
   */
  exitScope() {
    if (this.scopes.length > 1) {
      this.scopes.pop();
      this.currentScope = this.scopes[this.scopes.length - 1];
    }
  }

  /**
   * Get SMT variable name for a program variable
   * @param {string} varName - Original variable name
   * @returns {string} SMT variable name
   */
  getSMTVarName(varName) {
    // For basic implementation, we just escape the variable name
    // In a full implementation, this would handle SSA form variables
    return varName.replace(/[^a-zA-Z0-9_]/g, '_');
  }

  /**
   * Generate the full SMT-LIB script
   * @returns {string} Complete SMT-LIB script
   */
  generateSMTScript() {
    // Header with logic selection
    const header = [
      "(set-logic QF_LIA)", // Quantifier-Free Linear Integer Arithmetic
      "(set-option :produce-models true)"  // Enable model generation for counterexamples
    ];
    
    // Combine all parts
    return [
      ...header,
      ...this.declarations,
      ...this.assertions,
      "(check-sat)",
      "(get-model)"
    ].join('\n');
  }

  /**
   * Utility to convert SMT output to a more readable format
   * @param {string} smtOutput - Raw SMT solver output
   * @returns {Object} Parsed result
   */
  parseOutput(smtOutput) {
    if (smtOutput.startsWith("sat")) {
      // Parse model for variable values
      const model = {};
      const modelLines = smtOutput.split('\n').slice(1, -1).join('\n');
      
      // Very basic parsing - this would be more sophisticated in a real implementation
      const varMatches = modelLines.matchAll(/\(define-fun\s+(\w+)\s+.*?(\d+|\w+)\)/g);
      
      for (const match of varMatches) {
        if (match[1] && match[2]) {
          model[match[1]] = match[2];
        }
      }
      
      return {
        result: 'sat',
        model: model
      };
    } else if (smtOutput.startsWith("unsat")) {
      return {
        result: 'unsat',
        model: null
      };
    } else {
      return {
        result: 'unknown',
        model: null
      };
    }
  }
}

module.exports = new SMTGenerator();
