/**
 * SMT Generation Service
 * Provides high-level API for generating SMT constraints from programs
 */
const ssaToSmtTranslator = require('./ssaToSmtTranslator');

class SMTGenerationService {
  /**
   * Generate SMT constraints from program AST with support for arrays and control flow
   * @param {Object} ast - AST of the program
   * @param {Object} options - Generation options including loop unrolling depth
   * @returns {Object} SMT constraints
   */
  async generateConstraints(ast, options = {}) {
    try {
      console.log('Generating constraints with options:', options);
      
      // Extract variables, assertions, and arrays from the AST
      const variables = this.extractVariablesFromAST(ast);
      const assertions = this.extractAssertionsFromAST(ast);
      const arrays = this.extractArraysFromAST(ast);
      
      // Translate from SSA to SMT using the translator
      const smtResult = await ssaToSmtTranslator.translate(ast, {
        variables,
        arrays,
        assertions,
        loopUnrollDepth: options.loopUnrollDepth || 5
      });
      
      // Generate the full SMT script
      const smtScript = this.generateSMTScript({
        declarations: smtResult.declarations,
        assertions: smtResult.assertions,
        variables,
        arrays
      });
      
      // Create constraints object
      return {
        success: true,
        smtScript,
        declarations: smtResult.declarations,
        assertions: smtResult.assertions,
        variables: variables.map(v => v.name),
        arrays: arrays.map(a => a.name),
        statements: smtResult.statements
      };
    } catch (error) {
      console.error('Error generating SMT constraints:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Extract variables from AST
   * @param {Object} ast - Program AST
   * @returns {Array} Array of variable objects
   */
  extractVariablesFromAST(ast) {
    const variables = [];
    const visited = new Set();
    
    // Function to recursively extract variables from AST nodes
    const extract = (node) => {
      if (!node) return;
      
      // Process node based on type
      if (node.type === 'VariableDeclaration' && node.id && node.id.name) {
        const varName = node.id.name;
        
        // Only add each variable once
        if (!visited.has(varName)) {
          visited.add(varName);
          variables.push({
            name: varName,
            type: node.valueType || 'Int', // Default type is Int
            node
          });
        }
      } else if (node.type === 'AssignmentStatement' && node.left && node.left.name) {
        const varName = node.left.name;
        
        // Only add each variable once
        if (!visited.has(varName)) {
          visited.add(varName);
          variables.push({
            name: varName,
            type: 'Int', // Default type is Int
            node
          });
        }
      }
      
      // Recursively process child nodes
      if (node.body && Array.isArray(node.body)) {
        for (const child of node.body) {
          extract(child);
        }
      }
      
      // Process if statement branches
      if (node.type === 'IfStatement') {
        extract(node.consequent);
        if (node.alternate) {
          extract(node.alternate);
        }
      }
      
      // Process loop bodies
      if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
        extract(node.body);
      }
      
      // Process initialization, condition, and update in for loops
      if (node.type === 'ForStatement') {
        if (node.init) extract(node.init);
        if (node.update) extract(node.update);
      }
    };
    
    // Start extraction from the root of the AST
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        extract(node);
      }
    } else {
      extract(ast);
    }
    
    return variables;
  }

  /**
   * Extract assertions from AST
   * @param {Object} ast - Program AST
   * @returns {Array} Array of assertion objects
   */
  extractAssertionsFromAST(ast) {
    const assertions = [];
    
    // Function to recursively extract assertions from AST nodes
    const extract = (node) => {
      if (!node) return;
    
      // Process assert statements
      if (node.type === 'AssertStatement' && node.expression) {
        const expr = node.expression;
    assertions.push({
          constraint: this.expressionToSMT(expr),
          description: 'Assertion',
          node
        });
      }
      
      // Recursively process child nodes
      if (node.body && Array.isArray(node.body)) {
        for (const child of node.body) {
          extract(child);
        }
      }
      
      // Process if statement branches
      if (node.type === 'IfStatement') {
        extract(node.consequent);
        if (node.alternate) {
          extract(node.alternate);
        }
      }
      
      // Process loop bodies
      if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
        extract(node.body);
      }
    };
    
    // Start extraction from the root of the AST
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        extract(node);
      }
    } else {
      extract(ast);
    }
    
    return assertions;
  }

  /**
   * Extract arrays from AST
   * @param {Object} ast - Program AST
   * @returns {Array} Array of array objects
   */
  extractArraysFromAST(ast) {
    const arrays = [];
    const visited = new Set();
    
    // Function to recursively extract arrays from AST nodes
    const extract = (node) => {
      if (!node) return;
      
      // Process array declarations
      if (node.type === 'ArrayDeclaration' && node.id && node.id.name) {
        const arrayName = node.id.name;
        
        // Only add each array once
        if (!visited.has(arrayName)) {
          visited.add(arrayName);
          arrays.push({
            name: arrayName,
            size: node.size?.value || 10,
            elementType: node.elementType || 'Int'
          });
        }
      }
      
      // Process array accesses (implicit array declarations)
      if (node.type === 'ArrayAccess' && node.array && node.array.name) {
        const arrayName = node.array.name;
        
        // Only add each array once
        if (!visited.has(arrayName)) {
          visited.add(arrayName);
          arrays.push({
            name: arrayName,
            size: 10, // Default size
            elementType: 'Int' // Default element type
          });
        }
      }
      
      // Process array assignments
      if (node.type === 'ArrayAssignment' && node.array && node.array.name) {
        const arrayName = node.array.name;
        
        // Only add each array once
        if (!visited.has(arrayName)) {
          visited.add(arrayName);
          arrays.push({
            name: arrayName,
            size: 10, // Default size
            elementType: 'Int' // Default element type
          });
        }
      }
      
      // Recursively process child nodes
      if (node.body && Array.isArray(node.body)) {
        for (const child of node.body) {
          extract(child);
        }
      }
      
      // Process if statement branches
      if (node.type === 'IfStatement') {
        extract(node.consequent);
        if (node.alternate) {
          extract(node.alternate);
        }
      }
      
      // Process loop bodies
      if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
        extract(node.body);
      }
    };
    
    // Start extraction from the root of the AST
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        extract(node);
      }
    } else {
      extract(ast);
    }
    
    return arrays;
  }

  /**
   * Convert expression node to SMT constraint
   * @param {Object} expr - Expression node
   * @returns {string} SMT constraint
   */
  expressionToSMT(expr) {
    if (!expr) return '';
    
    // Handle different expression types
    if (expr.type === 'Literal') {
      return expr.value.toString();
    } else if (expr.type === 'Identifier') {
      return expr.name;
    } else if (expr.type === 'BinaryExpression') {
      const left = this.expressionToSMT(expr.left);
      const right = this.expressionToSMT(expr.right);
      const op = this.mapOperator(expr.operator);
      
      return `(${op} ${left} ${right})`;
    } else if (expr.type === 'UnaryExpression') {
      const operand = this.expressionToSMT(expr.argument);
      const op = this.mapOperator(expr.operator);
      
      return `(${op} ${operand})`;
    } else if (expr.type === 'ArrayAccess') {
      const array = expr.array.name;
      const index = this.expressionToSMT(expr.index);
      
      return `(select ${array} ${index})`;
    } else {
      // Default case, return a string representation
      return JSON.stringify(expr);
    }
  }

  /**
   * Map JavaScript operator to SMT-LIB operator
   * @param {string} operator - JavaScript operator
   * @returns {string} SMT-LIB operator
   */
  mapOperator(operator) {
    switch (operator) {
      case '+': return '+';
      case '-': return '-';
      case '*': return '*';
      case '/': return 'div';
      case '%': return 'mod';
      case '==': case '===': return '=';
      case '!=': case '!==': return 'not =';
      case '<': return '<';
      case '<=': return '<=';
      case '>': return '>';
      case '>=': return '>=';
      case '&&': return 'and';
      case '||': return 'or';
      case '!': return 'not';
      default: return operator;
    }
  }

  /**
   * Generate SMT script from declarations, assertions, variables, and arrays
   * @param {Object} options - Generation options
   * @param {Array} options.declarations - SMT declarations
   * @param {Array} options.assertions - SMT assertions
   * @param {Array} options.variables - Program variables
   * @param {Array} options.arrays - Program arrays
   * @returns {string} Complete SMT script
   */
  generateSMTScript(options) {
    const {
      declarations = [],
      assertions = [],
      variables = [],
      arrays = []
    } = options;

    let script = ';; SMT-LIB2 Script\n';
    script += '(set-logic QF_ALIA)\n\n';

    // Add declarations
    script += ';; Variable Declarations\n';
    for (const decl of declarations) {
      script += decl + '\n';
    }
    script += '\n';

    // Add assertions
    script += ';; Assertions\n';
    for (const assertion of assertions) {
      // Handle assertion objects or strings
      if (typeof assertion === 'string') {
        script += '(assert ' + assertion + ')\n';
      } else if (assertion.constraint) {
        const constraintStr = typeof assertion.constraint === 'string' 
          ? assertion.constraint
          : JSON.stringify(assertion.constraint);
        script += '(assert ' + constraintStr + ')\n';
      }
    }
    script += '\n';

    // Add check-sat and get-model commands
    script += ';; Check satisfiability\n';
    script += '(check-sat)\n';
    script += '(get-model)\n';
    
    return script;
  }

  /**
   * Generate constraints for checking program equivalence
   * @param {Object} ast1 - AST of first program
   * @param {Object} ast2 - AST of second program
   * @param {Object} options - Generation options
   * @returns {Object} SMT constraints for equivalence checking
   */
  async generateConstraintsForEquivalence(ast1, ast2, options = {}) {
    try {
      console.log('Generating constraints for equivalence with options:', options);
      
      // Extract variables and arrays from both programs
      const variables1 = this.extractVariablesFromAST(ast1);
      const variables2 = this.extractVariablesFromAST(ast2);
      const arrays1 = this.extractArraysFromAST(ast1);
      const arrays2 = this.extractArraysFromAST(ast2);
      
      console.log('Variables in program 1:', variables1.map(v => typeof v === 'string' ? v : v.name));
      console.log('Variables in program 2:', variables2.map(v => typeof v === 'string' ? v : v.name));
      
      // Generate SMT for both programs
      const smtResult1 = await ssaToSmtTranslator.translate(ast1, {
        variables: variables1,
        arrays: arrays1,
        assertions: [],
        loopUnrollDepth: options.loopUnrollDepth || 5,
        outputPrefix: 'prog1_'
      });
      
      const smtResult2 = await ssaToSmtTranslator.translate(ast2, {
        variables: variables2,
        arrays: arrays2,
        assertions: [],
        loopUnrollDepth: options.loopUnrollDepth || 5,
        outputPrefix: 'prog2_'
      });
      
      // Print SSA translation results
      console.log('Program 1 declarations:', smtResult1.declarations);
      console.log('Program 2 declarations:', smtResult2.declarations);
      
      // Combine declarations
      const declarations = [
        ...smtResult1.declarations,
        ...smtResult2.declarations
      ];
      
      // First, include all assertions from both programs
      const combinedAssertions = [
        ...smtResult1.assertions,
        ...smtResult2.assertions
      ];
      
      // Log combined assertions
      console.log('Combined assertions:', combinedAssertions);
      
      // Generate assertions that check output equivalence
      const equivalenceAssertions = [];
      const outputVars = options.outputVars || [];
      
      // Default focus variable is 'result' if not specified
      const checkVars = outputVars.length > 0 ? outputVars : ['result'];
      let inequalityCondition = null;
      
      console.log('Checking variables for equivalence:', checkVars);
      
      // For program equivalence, we specifically want to check the result or specified output variables
      // In most of our examples, this is the 'result' variable
      for (const varName of checkVars) {
        const hasVar1 = variables1.some(v => (typeof v === 'string' ? v : v.name) === varName);
        const hasVar2 = variables2.some(v => (typeof v === 'string' ? v : v.name) === varName);
        
        console.log(`Variable ${varName} presence: prog1=${hasVar1}, prog2=${hasVar2}`);
        
        // Only check variables that exist in both programs
        if (hasVar1 && hasVar2) {
          // This is the key assertion for equivalence checking!
          inequalityCondition = `(not (= prog1_${varName}_final prog2_${varName}_final))`;
          console.log(`Created primary equivalence condition: ${inequalityCondition}`);
        }
      }
      
      // If no common output variable found, try using all common variables
      if (!inequalityCondition) {
        // Get all variables that appear in both programs
        const commonVars = variables1
          .map(v => typeof v === 'string' ? v : v.name)
          .filter(name => variables2.some(v => (typeof v === 'string' ? v : v.name) === name));
        
        console.log('Common variables:', commonVars);
        
        // Focus on typical output variables first if they exist
        const potentialOutputVars = commonVars.filter(name => 
          name === 'result' || name === 'output' || name.includes('result') || name.includes('output')
        );
        
        console.log('Potential output variables:', potentialOutputVars);
        
        if (potentialOutputVars.length > 0) {
          // Use the most likely output variable
          inequalityCondition = `(not (= prog1_${potentialOutputVars[0]}_final prog2_${potentialOutputVars[0]}_final))`;
          console.log(`Using potential output variable: ${inequalityCondition}`);
        } else if (commonVars.length > 0) {
          // Generate OR conditions for all common variables
          const conditions = commonVars.map(varName => 
            `(not (= prog1_${varName}_final prog2_${varName}_final))`
          );
          
          inequalityCondition = conditions.length === 1 
            ? conditions[0] 
            : `(or ${conditions.join(' ')})`;
          console.log(`Using common variables for equivalence check: ${inequalityCondition}`);
        }
      }
      
      // Add the inequality assertion if we found variables to compare
      if (inequalityCondition) {
        equivalenceAssertions.push({
          constraint: inequalityCondition,
          description: 'Check if programs are equivalent'
        });
      }
      
      // Combine all assertions
      const assertions = [
        ...combinedAssertions,
        ...equivalenceAssertions
      ];
      
      // Generate combined SMT script
      const smtScript = this.generateSMTScript({
        declarations,
        assertions,
        variables: [
          ...variables1.map(v => `prog1_${typeof v === 'string' ? v : v.name}_final`),
          ...variables2.map(v => `prog2_${typeof v === 'string' ? v : v.name}_final`)
        ],
        arrays: [
          ...arrays1.map(a => `prog1_${typeof a === 'string' ? a : a.name}_final`), 
          ...arrays2.map(a => `prog2_${typeof a === 'string' ? a : a.name}_final`)
        ]
      });
      
      console.log('Generated SMT script (preview):', smtScript.substring(0, 500) + '...');
      
      return {
        success: true,
        smtScript,
        declarations,
        assertions,
        variables: [
          ...variables1.map(v => `prog1_${typeof v === 'string' ? v : v.name}`),
          ...variables2.map(v => `prog2_${typeof v === 'string' ? v : v.name}`),
          ...variables1.map(v => `prog1_${typeof v === 'string' ? v : v.name}_final`),
          ...variables2.map(v => `prog2_${typeof v === 'string' ? v : v.name}_final`)
        ],
        arrays: [
          ...arrays1.map(a => `prog1_${typeof a === 'string' ? a : a.name}`), 
          ...arrays2.map(a => `prog2_${typeof a === 'string' ? a : a.name}`),
          ...arrays1.map(a => `prog1_${typeof a === 'string' ? a : a.name}_final`), 
          ...arrays2.map(a => `prog2_${typeof a === 'string' ? a : a.name}_final`)
        ],
        statements: [...smtResult1.statements, ...smtResult2.statements]
      };
    } catch (error) {
      console.error('Error generating equivalence constraints:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }
}

// Export singleton instance
module.exports = new SMTGenerationService();
