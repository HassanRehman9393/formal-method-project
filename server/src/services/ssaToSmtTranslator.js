/**
 * SSA to SMT Translator
 * Converts SSA form to SMT constraints
 */
const smtLibGenerator = require('./smtLibGenerator');

class SSAToSMTTranslator {
  constructor() {
    this.declarations = [];
    this.assertions = [];
    this.variables = new Set();
    this.arrayVariables = new Set();
  }

  /**
   * Reset the translator state
   */
  reset() {
    this.declarations = [];
    this.assertions = [];
    this.variables = new Set();
    this.arrayVariables = new Set();
  }

  /**
   * Translate SSA program to SMT constraints
   * @param {Object} ssaProgram - Program in SSA form
   * @returns {Object} SMT constraints
   */
  translate(ssaProgram) {
    this.reset();
    
    if (!ssaProgram || !ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
      throw new Error('Invalid SSA program structure');
    }
    
    // Process each block in the SSA program
    for (const block of ssaProgram.blocks) {
      this.processBlock(block);
    }
    
    // Generate the SMT script
    const smtScript = this.generateSMTScript();
    
    return {
      success: true,
      smtScript,
      declarations: this.declarations,
      assertions: this.assertions,
      variables: Array.from(this.variables),
      arrays: Array.from(this.arrayVariables)
    };
  }

  /**
   * Process an SSA block
   * @param {Object} block - SSA block
   */
  processBlock(block) {
    if (!block) return;
    
    // Process phi functions
    if (block.phiFunctions && Array.isArray(block.phiFunctions)) {
      for (const phi of block.phiFunctions) {
        this.processPhiFunction(phi);
      }
    }
    
    // Process instructions
    if (block.instructions && Array.isArray(block.instructions)) {
      for (const instr of block.instructions) {
        this.processInstruction(instr);
      }
    }
    
    // Process terminator
    if (block.terminator) {
      this.processTerminator(block.terminator);
    }
  }

  /**
   * Process a phi function
   * @param {Object} phi - Phi function
   */
  processPhiFunction(phi) {
    if (!phi) return;
    
    // Register the variable
    this.registerVariable(phi.target);
    
    // For each source in the phi function
    const sources = phi.sources || [];
    if (sources.length === 0) return;
    
    // In SMT, we use if-then-else to represent phi functions
    // For example: phi(x_1, x_2) where x_1 is from path1 and x_2 from path2
    // becomes (ite path1 x_1 x_2)
    
    // This is a simplified implementation
    // In a real system, you'd need to use the path conditions
    let phiValue = `${phi.variable}_${sources[0]}`;
    
    for (let i = 1; i < sources.length; i++) {
      // We need the path conditions to create proper ITE expressions
      // This is placeholder logic
      const pathCondition = `from_${sources[i]}`; // Should be actual path condition
      
      // Build nested ITE expressions
      phiValue = smtLibGenerator.generateITE(
        pathCondition,
        `${phi.variable}_${sources[i]}`,
        phiValue
      );
    }
    
    // Create assignment for the phi function result
    const assertion = smtLibGenerator.generateAssignment(phi.target, phiValue);
    this.assertions.push(assertion);
  }

  /**
   * Process an SSA instruction
   * @param {Object} instr - SSA instruction
   */
  processInstruction(instr) {
    if (!instr) return;
    
    // Handle different types of instructions
    if (instr.type === 'Comment') {
      // Skip comments in SMT generation
      return;
    } else if (instr.constructor && instr.constructor.name === 'Assignment') {
      // Handle regular assignment
      const target = instr.target;
      const value = this.processExpression(instr.value);
      
      // Register the variable
      this.registerVariable(target);
      
      // Create assignment assertion
      const assertion = smtLibGenerator.generateAssignment(target, value);
      this.assertions.push(assertion);
    } else if (instr.type === 'Assert') {
      // Handle assert statements
      const condition = this.processExpression(instr.condition);
      const assertion = smtLibGenerator.generateAssertion(condition);
      this.assertions.push(assertion);
    } else if (instr.type === 'ArrayAssignment') {
      // Handle array assignments
      const array = this.processExpression(instr.array);
      const index = this.processExpression(instr.index);
      const value = this.processExpression(instr.value);
      
      // Register as array variable
      this.arrayVariables.add(String(array).split('_')[0]); // Base name without version
      
      // Create array assignment
      const assertion = smtLibGenerator.generateArrayAssignment(array, index, value);
      this.assertions.push(assertion);
    }
  }

  /**
   * Process a terminator instruction
   * @param {Object} terminator - Terminator instruction
   */
  processTerminator(terminator) {
    if (!terminator) return;
    
    if (terminator.type === 'Branch') {
      // For branches, the condition becomes part of path conditions
      // In a full implementation, we'd track these for use in phi functions
      const condition = this.processExpression(terminator.condition);
      
      // We don't directly generate SMT for control flow,
      // as that's already encoded in how we use phi functions
    } else if (terminator.type === 'Return') {
      // For return statements, we might want to record the return value
      // for verification purposes
      if (terminator.value !== undefined) {
        const returnValue = this.processExpression(terminator.value);
        const returnVar = 'return_value';
        
        // Register the return value variable
        this.registerVariable(returnVar);
        
        // Create assignment for return value
        const assertion = smtLibGenerator.generateAssignment(returnVar, returnValue);
        this.assertions.push(assertion);
      }
    }
  }

  /**
   * Process an expression
   * @param {*} expr - Expression to process
   * @returns {string} SMT expression
   */
  processExpression(expr) {
    if (expr === null || expr === undefined) {
      return 'undefined';
    }
    
    if (typeof expr === 'string' || typeof expr === 'number' || typeof expr === 'boolean') {
      return String(expr);
    }
    
    if (!expr || typeof expr !== 'object') {
      return 'invalid_expression';
    }
    
    switch (expr.type) {
      case 'BinaryExpression':
        const left = this.processExpression(expr.left);
        const right = this.processExpression(expr.right);
        
        switch (expr.operator) {
          // Arithmetic
          case '+': return smtLibGenerator.generateArithmetic('+', left, right);
          case '-': return smtLibGenerator.generateArithmetic('-', left, right);
          case '*': return smtLibGenerator.generateArithmetic('*', left, right);
          case '/': return smtLibGenerator.generateArithmetic('/', left, right);
          case '%': return smtLibGenerator.generateArithmetic('%', left, right);
          
          // Comparison
          case '==': return smtLibGenerator.generateComparison('==', left, right);
          case '!=': return smtLibGenerator.generateComparison('!=', left, right);
          case '<': return smtLibGenerator.generateComparison('<', left, right);
          case '<=': return smtLibGenerator.generateComparison('<=', left, right);
          case '>': return smtLibGenerator.generateComparison('>', left, right);
          case '>=': return smtLibGenerator.generateComparison('>=', left, right);
          
          // Logical
          case '&&': return smtLibGenerator.generateLogical('&&', left, right);
          case '||': return smtLibGenerator.generateLogical('||', left, right);
          
          default:
            console.warn(`Unsupported binary operator: ${expr.operator}`);
            return 'unsupported_operator';
        }
        
      case 'UnaryExpression':
        const operand = this.processExpression(expr.operand);
        
        switch (expr.operator) {
          case '-': return `(- ${operand})`;
          case '!': return smtLibGenerator.generateNot(operand);
          case '+': return operand; // Unary plus doesn't change value
          
          default:
            console.warn(`Unsupported unary operator: ${expr.operator}`);
            return 'unsupported_operator';
        }
        
      case 'ArrayAccess':
        const array = this.processExpression(expr.array);
        const index = this.processExpression(expr.index);
        
        // Register as array variable
        this.arrayVariables.add(String(array).split('_')[0]); // Base name without version
        
        return smtLibGenerator.generateArraySelect(array, index);
        
      default:
        return `${expr.type || 'unknown'}`;
    }
  }

  /**
   * Register a variable for declaration
   * @param {string} varName - Variable name
   */
  registerVariable(varName) {
    if (!this.variables.has(varName)) {
      this.variables.add(varName);
      
      // For simplicity, we assume all variables are integers
      // In a real implementation, you'd need to track types
      const declaration = smtLibGenerator.generateDeclaration(varName, 'Int');
      this.declarations.push(declaration);
    }
  }

  /**
   * Generate the full SMT script
   * @returns {string} Complete SMT-LIB script
   */
  generateSMTScript() {
    // Define the logic to use
    // QF_ALIA - Arrays and Linear Integer Arithmetic
    const header = [
      "(set-logic QF_ALIA)",
      "(set-option :produce-models true)"
    ];
    
    // For each array variable, add an array declaration
    const arrayDeclarations = Array.from(this.arrayVariables).map(array => 
      smtLibGenerator.generateArrayDeclaration(array, 'Int', 'Int')
    );
    
    // Combine all parts
    return [
      ...header,
      ...arrayDeclarations,
      ...this.declarations,
      ...this.assertions,
      "(check-sat)",
      "(get-model)"
    ].join('\n');
  }
}

module.exports = new SSAToSMTTranslator();
