/**
 * SSA to SMT Translator Service
 * Converts Static Single Assignment (SSA) form to SMT constraints
 */

class SSAToSMTTranslator {
  constructor() {
    console.log('[SSAToSMTTranslator] Initialized');
  }

  /**
   * Translate SSA AST to SMT constraints
   * @param {Object} ssaAst - Program AST in SSA form
   * @param {Object} options - Translation options
   * @returns {Object} - SMT constraints
   */
  async translate(ssaAst, options = {}) {
    console.log('[SSAToSMTTranslator] Translating SSA to SMT');
    
    try {
      const declarations = [];
      const assertions = [];
      const statements = [];
      
      // Extract variables and arrays
      const variables = options.variables || [];
      const arrays = options.arrays || [];
      const outputPrefix = options.outputPrefix || '';
      
      // Create variable mapping to handle SSA form consistently
      const variableMap = new Map();
      
      // Always use the non-final version for variable references in the code
      // and create linking constraints to the final versions
      for (const variable of variables) {
        const name = typeof variable === 'string' ? variable : variable.name;
        const type = (typeof variable === 'object' && variable.type) ? variable.type : 'Int';
        
        // Declare the basic variable
        declarations.push(`(declare-const ${outputPrefix}${name} ${type})`);
        variableMap.set(name, `${outputPrefix}${name}`);
        
        // Declare all specialized versions of the variable in SSA form
        const versions = this.findVariableVersions(ssaAst, name);
        
        for (const version of versions) {
          if (version !== name) {
            declarations.push(`(declare-const ${outputPrefix}${version} ${type})`);
            variableMap.set(version, `${outputPrefix}${version}`);
          }
        }
        
        // Always declare the final version
        const finalVersion = `${name}_final`;
        declarations.push(`(declare-const ${outputPrefix}${finalVersion} ${type})`);
        variableMap.set(finalVersion, `${outputPrefix}${finalVersion}`);
        
        // If we have any SSA versions, find the last one and link to final
        if (versions.length > 0) {
          const lastVersion = this.findFinalVersion(ssaAst, name);
          if (lastVersion) {
            assertions.push({
              constraint: `(= ${outputPrefix}${finalVersion} ${outputPrefix}${lastVersion})`,
              description: `Link final version of ${name} to last SSA version`
            });
          } else {
            // If no SSA versions found, link final to the base variable
            assertions.push({
              constraint: `(= ${outputPrefix}${finalVersion} ${outputPrefix}${name})`,
              description: `Link final version of ${name} to base variable`
            });
          }
        } else {
          // If no versions at all, make sure final version equals regular version
          assertions.push({
            constraint: `(= ${outputPrefix}${finalVersion} ${outputPrefix}${name})`,
            description: `Link final version of ${name} to regular version`
          });
        }
      }
      
      // Declare arrays with the same pattern
      for (const array of arrays) {
        const name = typeof array === 'string' ? array : array.name;
        const elementType = (typeof array === 'object' && array.elementType) ? array.elementType : 'Int';
        
        // Declare basic array
        declarations.push(`(declare-const ${outputPrefix}${name} (Array Int ${elementType}))`);
        variableMap.set(name, `${outputPrefix}${name}`);
        
        // Declare all specialized versions of the array in SSA form
        const versions = this.findArrayVersions(ssaAst, name);
        
        for (const version of versions) {
          if (version !== name) {
            declarations.push(`(declare-const ${outputPrefix}${version} (Array Int ${elementType}))`);
            variableMap.set(version, `${outputPrefix}${version}`);
          }
        }
        
        // Always declare the final version
        const finalVersion = `${name}_final`;
        declarations.push(`(declare-const ${outputPrefix}${finalVersion} (Array Int ${elementType}))`);
        variableMap.set(finalVersion, `${outputPrefix}${finalVersion}`);
        
        // If we have any SSA versions, find the last one and link to final
        if (versions.length > 0) {
          const lastVersion = this.findFinalVersion(ssaAst, name);
          if (lastVersion) {
            assertions.push({
              constraint: `(= ${outputPrefix}${finalVersion} ${outputPrefix}${lastVersion})`,
              description: `Link final version of ${name} to last SSA version`
            });
          } else {
            // If no SSA versions found, link final to the base array
            assertions.push({
              constraint: `(= ${outputPrefix}${finalVersion} ${outputPrefix}${name})`,
              description: `Link final version of ${name} to base array`
            });
          }
        } else {
          // If no versions at all, make sure final version equals regular version
          assertions.push({
            constraint: `(= ${outputPrefix}${finalVersion} ${outputPrefix}${name})`,
            description: `Link final version of ${name} to regular version`
          });
        }
      }
      
      // Generate constraints from SSA AST
      const constraints = this.generateConstraints(ssaAst, {
        variables,
        arrays,
        outputPrefix,
        variableMap
      });
      
      // Add constraints to assertions
      for (const constraint of constraints) {
        assertions.push({
          constraint,
          description: 'SSA constraint'
        });
      }
      
      // Add any assertions that were passed in
      const userAssertions = options.assertions || [];
      for (const assertion of userAssertions) {
        if (typeof assertion === 'string') {
          assertions.push({
            constraint: assertion,
            description: 'User assertion'
          });
        } else if (assertion.constraint) {
          assertions.push(assertion);
        }
      }
      
      // Extract statements for execution trace
      const extractedStatements = this.extractStatements(ssaAst);
      for (const stmt of extractedStatements) {
        statements.push(stmt);
      }
    
    return {
      success: true,
        declarations,
        assertions,
        statements
      };
    } catch (error) {
      console.error('[SSAToSMTTranslator] Error translating SSA to SMT:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Find all versions of a variable in SSA form
   * @param {Object} ast - AST in SSA form
   * @param {String} varName - Base variable name
   * @returns {Array} - Array of variable versions
   */
  findVariableVersions(ast, varName) {
    const versions = new Set();
    
    // Function to recursively search for variable versions
    const search = (node) => {
      if (!node) return;
      
      // Check if node is an identifier with the base name
      if (node.type === 'Identifier' && node.name.startsWith(varName + '_')) {
        versions.add(node.name);
      } else if (node.type === 'Identifier' && node.name === varName) {
        versions.add(node.name);
      }
      
      // Check for assignment target
      if (node.type === 'AssignmentStatement' && node.left && node.left.name) {
        if (node.left.name.startsWith(varName + '_') || node.left.name === varName) {
          versions.add(node.left.name);
        }
      }
      
      // Recursively search child nodes
      if (node.body && Array.isArray(node.body)) {
        for (const child of node.body) {
          search(child);
        }
      }
      
      // Search in expression subtrees
      if (node.left) search(node.left);
      if (node.right) search(node.right);
      if (node.condition) search(node.condition);
      if (node.expression) search(node.expression);
      if (node.alternate) search(node.alternate);
      if (node.consequent) search(node.consequent);
      if (node.init) search(node.init);
      if (node.update) search(node.update);
    };
    
    // Start search from AST root
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        search(node);
      }
    } else {
      search(ast);
    }
    
    return Array.from(versions);
  }

  /**
   * Find all versions of an array in SSA form
   * @param {Object} ast - AST in SSA form
   * @param {String} arrayName - Base array name
   * @returns {Array} - Array of array versions
   */
  findArrayVersions(ast, arrayName) {
    const versions = new Set();
    
    // Function to recursively search for array versions
    const search = (node) => {
      if (!node) return;
      
      // Check for array access
      if (node.type === 'ArrayAccess' && node.array && node.array.name) {
        if (node.array.name.startsWith(arrayName + '_') || node.array.name === arrayName) {
          versions.add(node.array.name);
        }
      }
      
      // Check for array assignment
      if (node.type === 'ArrayAssignment' && node.array && node.array.name) {
        if (node.array.name.startsWith(arrayName + '_') || node.array.name === arrayName) {
          versions.add(node.array.name);
        }
      }
      
      // Recursively search child nodes
      if (node.body && Array.isArray(node.body)) {
        for (const child of node.body) {
          search(child);
        }
      }
      
      // Search in expression subtrees
      if (node.left) search(node.left);
      if (node.right) search(node.right);
      if (node.condition) search(node.condition);
      if (node.expression) search(node.expression);
      if (node.alternate) search(node.alternate);
      if (node.consequent) search(node.consequent);
      if (node.init) search(node.init);
      if (node.update) search(node.update);
      if (node.index) search(node.index);
      if (node.value) search(node.value);
    };
    
    // Start search from AST root
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        search(node);
      }
    } else {
      search(ast);
    }
    
    return Array.from(versions);
  }

  /**
   * Find the final version of a variable in SSA form
   * @param {Object} ast - AST in SSA form
   * @param {String} varName - Base variable name
   * @returns {String} - Final variable version
   */
  findFinalVersion(ast, varName) {
    const versions = this.findVariableVersions(ast, varName);
    
    if (versions.length === 0) {
      return `${varName}_final`;
    }
    
    // Sort versions by their numeric suffix
    const sortedVersions = versions.sort((a, b) => {
      const aParts = a.split('_');
      const bParts = b.split('_');
      
      // If no numeric suffix, treat as 0
      const aNum = aParts.length > 1 ? parseInt(aParts[aParts.length - 1]) : 0;
      const bNum = bParts.length > 1 ? parseInt(bParts[bParts.length - 1]) : 0;
      
      return bNum - aNum; // Descending order
    });
    
    return sortedVersions[0] || `${varName}_final`;
  }

  /**
   * Generate SMT constraints from SSA AST
   * @param {Object} ast - AST in SSA form
   * @param {Object} options - Generation options
   * @returns {Array} - Array of SMT constraints
   */
  generateConstraints(ast, options = {}) {
    const constraints = [];
    const outputPrefix = options.outputPrefix || '';
    const variableMap = options.variableMap || new Map();
    
    // Function to recursively generate constraints
    const process = (node) => {
      if (!node) return;
      
      // Process node based on type
      if (node.type === 'AssignmentStatement' || node.type === 'VariableDeclaration') {
        // Handle assignments: either direct assignments or variable declarations with initialization
        let left, right;
        
        if (node.type === 'AssignmentStatement') {
          left = node.left ? (typeof node.left === 'string' ? node.left : node.left.name) : '';
          right = node.right ? this.expressionToSMT(node.right, outputPrefix, variableMap) : '0';
        } else if (node.type === 'VariableDeclaration') {
          left = node.id ? (typeof node.id === 'string' ? node.id : node.id.name) : '';
          right = node.init ? this.expressionToSMT(node.init, outputPrefix, variableMap) : '0';
        }
        
        if (left) {
          const leftVar = variableMap.get(left) || `${outputPrefix}${left}`;
          constraints.push(`(= ${leftVar} ${right})`);
        }
      } else if (node.type === 'ArrayAssignment') {
        const array = node.array ? (typeof node.array === 'string' ? node.array : node.array.name) : '';
        const index = node.index ? this.expressionToSMT(node.index, outputPrefix, variableMap) : '0';
        const value = node.value ? this.expressionToSMT(node.value, outputPrefix, variableMap) : '0';
        
        if (array) {
          const arrayVar = variableMap.get(array) || `${outputPrefix}${array}`;
          constraints.push(`(= ${arrayVar} (store ${arrayVar} ${index} ${value}))`);
        }
      } else if (node.type === 'IfStatement') {
        // Process if-then-else statements
        const condition = node.condition ? this.expressionToSMT(node.condition, outputPrefix, variableMap) : 'true';
        
        // Process consequent branch
        if (node.consequent) {
          if (node.consequent.body && Array.isArray(node.consequent.body)) {
            for (const child of node.consequent.body) {
              process(child);
            }
          } else {
            process(node.consequent);
          }
        }
        
        // Process alternate branch
        if (node.alternate) {
          if (node.alternate.body && Array.isArray(node.alternate.body)) {
            for (const child of node.alternate.body) {
              process(child);
            }
          } else {
            process(node.alternate);
          }
        }
        
        // Add constraint for the condition
        if (condition !== 'true') {
          constraints.push(condition);
        }
      } else if (node.type === 'AssertStatement') {
        const expression = node.expression ? this.expressionToSMT(node.expression, outputPrefix, variableMap) : '';
        
        if (expression) {
          constraints.push(expression);
        }
      }
      
      // Recursively process child nodes
      if (node.body && Array.isArray(node.body)) {
        for (const child of node.body) {
          process(child);
        }
      }
    };
    
    // Start processing from the root of the AST
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        process(node);
      }
    } else {
      process(ast);
    }
    
    return constraints;
  }

  /**
   * Extract statements from AST for execution trace
   * @param {Object} ast - AST
   * @returns {Array} - Statements
   */
  extractStatements(ast) {
    const statements = [];
    
    // Function to recursively extract statements
    const extract = (node, line = 0) => {
      if (!node) return;
      
      // Extract statements based on node type
      if (node.type === 'VariableDeclaration') {
        const varName = node.id ? node.id.name : 'var';
        const initValue = node.init ? JSON.stringify(node.init) : '0';
        
        statements.push({
          line: node.line || line,
          text: `${varName} := ${initValue}`,
          type: 'VariableDeclaration',
          updates: [{ variable: varName, value: parseFloat(initValue) || 0 }]
        });
      } else if (node.type === 'AssignmentStatement') {
        const left = node.left ? node.left.name : '';
        const right = node.right ? JSON.stringify(node.right) : '0';
        
        statements.push({
          line: node.line || line,
          text: `${left} := ${right}`,
          type: 'AssignmentStatement',
          updates: [{ variable: left, value: parseFloat(right) || 0 }]
        });
      } else if (node.type === 'ArrayAssignment') {
        const array = node.array ? node.array.name : '';
        const index = node.index ? JSON.stringify(node.index) : '0';
        const value = node.value ? JSON.stringify(node.value) : '0';
        
        statements.push({
          line: node.line || line,
          text: `${array}[${index}] := ${value}`,
          type: 'ArrayAssignment',
          updates: [{ array, index: parseFloat(index) || 0, value: parseFloat(value) || 0 }]
        });
      } else if (node.type === 'AssertStatement') {
        const expression = node.expression ? JSON.stringify(node.expression) : '';
        
        statements.push({
          line: node.line || line,
          text: `assert(${expression})`,
          type: 'AssertStatement'
        });
      } else if (node.type === 'IfStatement') {
        const condition = node.condition ? JSON.stringify(node.condition) : '';
        
        statements.push({
          line: node.line || line,
          text: `if (${condition})`,
          type: 'IfStatement'
        });
        
        // Extract statements from consequent branch
        if (node.consequent) {
          if (node.consequent.body && Array.isArray(node.consequent.body)) {
            for (let i = 0; i < node.consequent.body.length; i++) {
              extract(node.consequent.body[i], line + i + 1);
            }
          } else {
            extract(node.consequent, line + 1);
          }
        }
        
        // Extract statements from alternate branch
        if (node.alternate) {
          statements.push({
            line: line + (node.consequent ? 1 : 0),
            text: 'else',
            type: 'ElseStatement'
          });
          
          if (node.alternate.body && Array.isArray(node.alternate.body)) {
            for (let i = 0; i < node.alternate.body.length; i++) {
              extract(node.alternate.body[i], line + (node.consequent ? 2 : 1) + i);
            }
          } else {
            extract(node.alternate, line + (node.consequent ? 2 : 1));
          }
        }
      } else if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
        const condition = node.condition ? JSON.stringify(node.condition) : '';
        
        statements.push({
          line: node.line || line,
          text: `${node.type === 'WhileStatement' ? 'while' : 'for'} (${condition})`,
          type: node.type
        });
        
        // Extract statements from loop body
        if (node.body) {
          if (node.body.body && Array.isArray(node.body.body)) {
            for (let i = 0; i < node.body.body.length; i++) {
              extract(node.body.body[i], line + i + 1);
            }
          } else {
            extract(node.body, line + 1);
          }
        }
      } else {
        // Generic statement
        statements.push({
          line: node.line || line,
          text: `${node.type || 'Statement'}`,
          type: node.type || 'Statement'
        });
      }
    };
    
    // Start extraction from the root of the AST
    let lineCounter = 1;
    if (ast.body && Array.isArray(ast.body)) {
      for (const node of ast.body) {
        extract(node, lineCounter);
        lineCounter += 1 + this.countNestedStatements(node);
      }
    } else {
      extract(ast, lineCounter);
    }
    
    return statements;
  }
  
  /**
   * Count the number of nested statements in a node
   * @param {Object} node - AST node
   * @returns {number} - Number of nested statements
   */
  countNestedStatements(node) {
    if (!node) return 0;
    
    let count = 0;
    
    if (node.body) {
      if (Array.isArray(node.body)) {
        for (const child of node.body) {
          count += 1 + this.countNestedStatements(child);
        }
      } else {
        count += 1 + this.countNestedStatements(node.body);
      }
    }
    
    if (node.consequent) {
      count += 1 + this.countNestedStatements(node.consequent);
    }
    
    if (node.alternate) {
      count += 1 + this.countNestedStatements(node.alternate);
    }
    
    return count;
  }

  /**
   * Convert an expression to SMT
   * @param {Object} expr - Expression node
   * @param {String} prefix - Variable prefix
   * @param {Map} variableMap - Map of variable names to their SMT counterparts
   * @returns {String} - SMT expression
   */
  expressionToSMT(expr, prefix = '', variableMap = new Map()) {
    if (!expr) return '0';
    
    // Handle different expression types
    if (typeof expr === 'number') {
      return expr.toString();
    } else if (typeof expr === 'boolean') {
      return expr ? 'true' : 'false';
    } else if (typeof expr === 'string') {
      // Check if this variable has a mapping
      return variableMap.get(expr) || `${prefix}${expr}`;
    }
    
    // Handle expression objects
    if (expr.type === 'Literal') {
      if (typeof expr.value === 'number') {
        return expr.value.toString();
      } else if (typeof expr.value === 'boolean') {
        return expr.value ? 'true' : 'false';
      } else {
        return `"${expr.value}"`;
      }
    } else if (expr.type === 'Identifier') {
      // Use the mapping if available
      const varName = expr.name;
      return variableMap.get(varName) || `${prefix}${varName}`;
    } else if (expr.type === 'BinaryExpression') {
      const left = this.expressionToSMT(expr.left, prefix, variableMap);
      const right = this.expressionToSMT(expr.right, prefix, variableMap);
      const op = this.mapOperator(expr.operator);
      
      // Format depends on operator
      return `(${op} ${left} ${right})`;
    } else if (expr.type === 'UnaryExpression') {
      const argument = this.expressionToSMT(expr.argument, prefix, variableMap);
      const op = this.mapOperator(expr.operator);
      
      return `(${op} ${argument})`;
    } else if (expr.type === 'MemberExpression') {
      const object = this.expressionToSMT(expr.object, prefix, variableMap);
      const property = expr.computed
        ? this.expressionToSMT(expr.property, prefix, variableMap)
        : expr.property.name;
      
      return `(select ${object} ${property})`;
    } else if (expr.type === 'CallExpression') {
      const callee = expr.callee.name;
      const args = expr.arguments.map(arg => this.expressionToSMT(arg, prefix, variableMap)).join(' ');
      
      return `(${callee} ${args})`;
    } else if (expr.type === 'LogicalExpression') {
      const left = this.expressionToSMT(expr.left, prefix, variableMap);
      const right = this.expressionToSMT(expr.right, prefix, variableMap);
      const op = this.mapOperator(expr.operator);
      
      return `(${op} ${left} ${right})`;
    } else if (expr.type === 'ConditionalExpression') {
      const test = this.expressionToSMT(expr.test, prefix, variableMap);
      const consequent = this.expressionToSMT(expr.consequent, prefix, variableMap);
      const alternate = this.expressionToSMT(expr.alternate, prefix, variableMap);
      
      return `(ite ${test} ${consequent} ${alternate})`;
    } else if (expr.type === 'ArrayExpression') {
      // For array expressions, define a constant array with elements
      // This is a simplified approach - in practice, array handling depends on the target solver
      const elements = expr.elements.map(el => this.expressionToSMT(el, prefix, variableMap));
      let result = '((as const (Array Int Int)) 0)'; // Start with empty array
      
      // Apply store operations for each element
      for (let i = 0; i < elements.length; i++) {
        result = `(store ${result} ${i} ${elements[i]})`;
      }
      
      return result;
    } else if (expr.type === 'RawExpression' && expr.value) {
      return expr.value;
    }
    
    // Default case, return a string representation
    return JSON.stringify(expr);
  }
  
  /**
   * Map JavaScript operator to SMT-LIB operator
   * @param {string} operator - JavaScript operator
   * @returns {string} - SMT-LIB operator
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
}

// Export singleton instance
module.exports = new SSAToSMTTranslator();
