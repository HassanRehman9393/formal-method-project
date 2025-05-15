/**
 * SSA Transformation Service
 * Transforms AST to Static Single Assignment (SSA) form
 */

const parserService = require('./parserService');

/**
 * Transform an AST to SSA form
 * @param {Object} ast - Abstract Syntax Tree
 * @param {Object} options - Transformation options
 * @param {number} options.loopUnrollDepth - Maximum depth for loop unrolling
 * @returns {Object} SSA transformation result
 */
exports.transformToSSA = async (ast, options = {}) => {
  try {
    console.log('[SSAService] transformToSSA called with AST type:', typeof ast);
    
    if (!ast) {
      return {
        success: false,
        error: 'No AST provided for SSA transformation'
      };
    }

    // Handle string AST (sometimes client might send stringified AST)
    if (typeof ast === 'string') {
      try {
        ast = JSON.parse(ast);
        console.log('[SSAService] Parsed string AST to object');
      } catch (parseError) {
        return {
          success: false,
          error: `Invalid AST string: ${parseError.message}`
        };
      }
    }

    const loopUnrollDepth = options.loopUnrollDepth || 5;
    console.log('[SSAService] Using loop unroll depth:', loopUnrollDepth);
    
    // Perform basic validation of the AST
    if (!ast.type || ast.type !== 'Program' || !ast.body || !Array.isArray(ast.body)) {
      console.error('[SSAService] Invalid AST structure:', JSON.stringify(ast).substring(0, 100));
      return {
        success: false,
        error: 'Invalid AST structure'
      };
    }

    // This is a placeholder implementation that would be replaced with actual SSA transformation
    // In a real implementation, this would convert the AST to SSA form
    const ssaAst = transformASTToSSA(ast, loopUnrollDepth);
    
    // Generate SSA code as a string representation
    const ssaCode = generateSSACode(ssaAst);
    
    // Generate optimized SSA code
    const optimizedSsaCode = optimizeSSA(ssaCode);
    
    return {
      success: true,
      ssaAst,
      ssaCode,
      optimizedSsaCode
    };
  } catch (error) {
    console.error('SSA transformation error:', error);
    return {
      success: false,
      error: `Error during SSA transformation: ${error.message}`
    };
  }
};

/**
 * Parse program code and transform to SSA
 * @param {string} programCode - Program code to transform
 * @param {Object} options - Transformation options
 * @returns {Object} SSA transformation result
 */
exports.parseAndTransformToSSA = async (programCode, options = {}) => {
  try {
    // Parse the code to get an AST
    const parseResult = await parserService.parseProgram(programCode);
    
    if (!parseResult.success) {
      return {
        success: false,
        error: `Parser error: ${parseResult.error}`
      };
    }
    
    // Transform the AST to SSA form
    const ssaResult = await exports.transformToSSA(parseResult.ast, options);
    
    return ssaResult;
  } catch (error) {
    console.error('Parse and transform error:', error);
    return {
      success: false,
      error: `Error during parsing and transformation: ${error.message}`
    };
  }
};

/**
 * Transform AST to SSA form (placeholder implementation)
 * @param {Object} ast - Abstract Syntax Tree
 * @param {number} loopUnrollDepth - Loop unrolling depth
 * @returns {Object} AST in SSA form
 */
function transformASTToSSA(ast, loopUnrollDepth) {
  // This is a simplified placeholder implementation
  // A real implementation would perform a proper SSA transformation
  
  // Create a deep copy of the AST to avoid modifying the original
  const ssaAST = JSON.parse(JSON.stringify(ast));
  
  // Add SSA information to the copy
  ssaAST.ssaForm = true;
  ssaAST.loopUnrollDepth = loopUnrollDepth;
  
  // Add version information to variables (placeholder)
  ssaAST.variables = {};
  
  // Return the SSA-transformed AST
  return ssaAST;
}

/**
 * Generate SSA code from SSA AST
 * @param {Object} ssaAST - AST in SSA form
 * @returns {string} SSA code
 */
function generateSSACode(ssaAST) {
  if (!ssaAST || !ssaAST.body || !Array.isArray(ssaAST.body)) {
    return "// Error: Unable to generate SSA code from invalid AST";
  }
  
  let ssaCode = "// Program in SSA form\n";
  
  // Process the statements in the AST
  ssaAST.body.forEach((node, index) => {
    const line = generateStatementSSA(node, index);
    if (line) {
      ssaCode += line + "\n";
    }
  });
  
  return ssaCode;
}

/**
 * Generate SSA code for a single statement
 * @param {Object} node - AST node
 * @param {number} index - Statement index for versioning
 * @returns {string} SSA code for the statement
 */
function generateStatementSSA(node, index) {
  if (!node) return null;
  
  switch (node.type) {
    case 'VariableDeclaration':
      if (node.id && node.init) {
        const varName = node.id.name || 'var';
        const initValue = expressionToString(node.init);
        return `${varName}_${index} := ${initValue};`;
      }
      return `// Variable declaration without name or initializer at index ${index}`;
      
    case 'AssignmentStatement':
      if (node.left && node.right) {
        const leftName = node.left.name || 'var';
        const rightValue = expressionToString(node.right);
        return `${leftName}_${index + 1} := ${rightValue};`;
      }
      return `// Assignment without left or right at index ${index}`;
      
    case 'AssertStatement':
      if (node.expression) {
        // Use the correct expression string conversion
        const exprStr = expressionToString(node.expression);
        // For SSA form, let's assume we use the version from the last statement
        // This isn't perfect SSA but works for our simple examples
        return `assert(${exprStr.replace(/\b([a-zA-Z_]\w*)\b(?!\s*\()/g, '$1_0')});`;
      }
      return `// Assert without expression at index ${index}`;
      
    case 'IfStatement':
      let ifCode = '';
      if (node.test) {
        // Convert the condition to proper string representation
        const conditionStr = expressionToString(node.test);
        // Update variable names to include version numbers
        const ssaCondition = conditionStr.replace(/\b([a-zA-Z_]\w*)\b(?!\s*\()/g, '$1_0');
        ifCode = `if (${ssaCondition}) {`;
      } else {
        ifCode = `if (/* missing condition */) {`;
      }
      
      // Process the then branch if it exists
      if (node.consequent && node.consequent.body) {
        ifCode += '\n';
        // Process each statement in the consequent
        for (const stmt of node.consequent.body) {
          const stmtStr = generateStatementSSA(stmt, index + 1);
          if (stmtStr) {
            ifCode += `  ${stmtStr}\n`;
          }
        }
      } else {
        ifCode += '\n  // Then branch would be processed here\n';
      }
      
      // Process the else branch if it exists
      if (node.alternate) {
        ifCode += '} else {';
        if (node.alternate.body) {
          ifCode += '\n';
          // Process each statement in the alternate
          for (const stmt of node.alternate.body) {
            const stmtStr = generateStatementSSA(stmt, index + 1);
            if (stmtStr) {
              ifCode += `  ${stmtStr}\n`;
            }
          }
        } else {
          ifCode += '\n  // Else branch would be processed here\n';
        }
        ifCode += '}';
      } else {
        ifCode += '}';
      }
      
      return ifCode;
      
    case 'WhileStatement':
      if (node.condition) {
        const conditionStr = expressionToString(node.condition);
        // Update variable names to include version numbers
        const ssaCondition = conditionStr.replace(/\b([a-zA-Z_]\w*)\b(?!\s*\()/g, '$1_0');
        return `while (${ssaCondition}) {\n  // Loop body would be processed here\n}`;
      }
      return `// While without condition at index ${index}`;
      
    default:
      return `// Unsupported statement type: ${node.type} at index ${index}`;
  }
}

/**
 * Convert expression to SSA string representation
 * @param {Object} expr - Expression node
 * @param {number} index - Statement index for versioning
 * @returns {string} SSA string for the expression
 */
function expressionToSSAString(expr, index) {
  if (!expr) return "/* undefined */";
  
  switch (expr.type) {
    case 'Identifier':
      const name = expr.name || 'var';
      // In SSA, we would use the latest version of the variable
      return `${name}_${index}`;
      
    case 'Literal':
      return expr.value !== undefined ? expr.value.toString() : "0";
      
    case 'BinaryExpression':
      const left = expressionToSSAString(expr.left, index);
      const right = expressionToSSAString(expr.right, index);
      const op = expr.operator || '?';
      return `${left} ${op} ${right}`;
      
    default:
      return `/* ${expr.type || 'unknown'} */`;
  }
}

/**
 * Convert expression to string
 * @param {Object} expr - Expression node
 * @returns {string} String representation of the expression
 */
function expressionToString(expr) {
  if (!expr) return "/* undefined */";
  
  switch (expr.type) {
    case 'Identifier':
      return expr.name || 'var';
      
    case 'Literal':
      return expr.value !== undefined ? expr.value.toString() : "0";
      
    case 'BinaryExpression':
      const left = expressionToString(expr.left);
      const right = expressionToString(expr.right);
      const op = expr.operator || '?';
      return `${left} ${op} ${right}`;
      
    default:
      return `/* ${expr.type || 'unknown'} */`;
  }
}

/**
 * Optimize SSA code with basic optimizations
 * @param {string} ssaCode - SSA code to optimize
 * @returns {string} Optimized SSA code
 */
function optimizeSSA(ssaCode) {
  // Split code into lines
  const lines = ssaCode.split('\n');
  let optimizedCode = "// Optimized SSA code with advanced optimizations\n";
  
  // Track variable information
  const constants = {}; // For constant propagation
  const expressions = {}; // For common subexpression elimination
  let inDeadCode = false; // Track if we're in a dead code block
  let ifIndentation = 0; // Track if statement indentation
  
  // First pass - identify constants and expressions
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    
    // Skip comments and empty lines
    if (line.startsWith('//') || line === '') {
      continue;
    }
    
    // Check for variable assignments with constant values
    const assignMatch = line.match(/^([a-zA-Z0-9_]+)_(\d+)\s*:=\s*(\d+);$/);
    if (assignMatch) {
      const [, varName, version, value] = assignMatch;
      constants[`${varName}_${version}`] = value;
      continue;
    }
    
    // Check for various conditional patterns that might be in our code
    const ifPatterns = [
      /^if\s+\(([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)\)\s*\{/,  // Common pattern: if (x_0 > 5) {
      /^if\s+\(\s*([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)\s*\)\s*\{/, // With more spaces
      /^if\s+\(\s*(.+?)\s*\)\s*\{/ // General if pattern to extract the condition
    ];
    
    for (const pattern of ifPatterns) {
      const match = line.match(pattern);
      if (match) {
        // If it's a simple comparison, we can directly check for constant values
        if (match.length >= 5) {
          const [, varName, version, operator, value] = match;
          const varKey = `${varName}_${version}`;
          
          if (constants[varKey]) {
            // Evaluate the condition statically
            const leftVal = parseInt(constants[varKey]);
            const rightVal = parseInt(value);
            let result = false;
            
            switch (operator) {
              case '==': result = leftVal === rightVal; break;
              case '!=': result = leftVal !== rightVal; break;
              case '>': result = leftVal > rightVal; break;
              case '<': result = leftVal < rightVal; break;
              case '>=': result = leftVal >= rightVal; break;
              case '<=': result = leftVal <= rightVal; break;
            }
            
            // Mark as dead code if condition is always false
            if (!result) {
              inDeadCode = true;
            }
          }
        } 
        // For more complex conditions, try to extract variables and expressions
        else if (match.length >= 2) {
          const condition = match[1];
          // Try to parse and evaluate the condition
          // Example: check for expressions like "x_0 > 5"
          const condParts = condition.match(/([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)/);
          if (condParts) {
            const [, varName, version, operator, value] = condParts;
            const varKey = `${varName}_${version}`;
            
            if (constants[varKey]) {
              // Evaluate the condition statically
              const leftVal = parseInt(constants[varKey]);
              const rightVal = parseInt(value);
              let result = false;
              
              switch (operator) {
                case '==': result = leftVal === rightVal; break;
                case '!=': result = leftVal !== rightVal; break;
                case '>': result = leftVal > rightVal; break;
                case '<': result = leftVal < rightVal; break;
                case '>=': result = leftVal >= rightVal; break;
                case '<=': result = leftVal <= rightVal; break;
              }
              
              // Mark as dead code if condition is always false
              if (!result) {
                inDeadCode = true;
              }
            }
          }
        }
        break;
      }
    }
    
    // Check for common subexpressions
    const exprMatch = line.match(/^([a-zA-Z0-9_]+)_(\d+)\s*:=\s*(.+);$/);
    if (exprMatch) {
      const [, varName, version, expression] = exprMatch;
      // Normalize the expression (remove spaces)
      const normalizedExpr = expression.replace(/\s+/g, '');
      
      // Check if we've seen this expression before
      if (expressions[normalizedExpr]) {
        expressions[normalizedExpr].targets.push(`${varName}_${version}`);
      } else {
        expressions[normalizedExpr] = {
          targets: [`${varName}_${version}`],
          original: expression
        };
      }
    }
  }
  
  // Second pass - generate optimized code with detailed comments
  inDeadCode = false; // Reset for second pass
  
  for (let i = 0; i < lines.length; i++) {
    let line = lines[i].trim();
    let explanation = [];
    
    // Skip comments and empty lines but preserve them
    if (line.startsWith('//') || line === '') {
      optimizedCode += line + '\n';
      continue;
    }
    
    // Check for end of if statement block that might be dead code
    if (line === '}') {
      if (inDeadCode) {
        inDeadCode = false;
        explanation.push("End of dead code block");
      }
      optimizedCode += line + (explanation.length > 0 ? ` // ${explanation.join(', ')}` : '') + '\n';
      continue;
    }
    
    // Check for various conditional patterns
    const ifPatterns = [
      /^if\s+\(([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)\)\s*\{/,
      /^if\s+\(\s*([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)\s*\)\s*\{/,
      /^if\s+\(\s*(.+?)\s*\)\s*\{/
    ];
    
    let ifMatch = null;
    for (const pattern of ifPatterns) {
      const match = line.match(pattern);
      if (match) {
        ifMatch = match;
        break;
      }
    }
    
    if (ifMatch) {
      // If it's a simple comparison, we can directly evaluate it
      if (ifMatch.length >= 5) {
        const [, varName, version, operator, value] = ifMatch;
        const varKey = `${varName}_${version}`;
        
        if (constants[varKey]) {
          // Evaluate the condition statically
          const leftVal = parseInt(constants[varKey]);
          const rightVal = parseInt(value);
          let result = false;
          
          switch (operator) {
            case '==': result = leftVal === rightVal; break;
            case '!=': result = leftVal !== rightVal; break;
            case '>': result = leftVal > rightVal; break;
            case '<': result = leftVal < rightVal; break;
            case '>=': result = leftVal >= rightVal; break;
            case '<=': result = leftVal <= rightVal; break;
          }
          
          if (!result) {
            inDeadCode = true;
            explanation.push(`Dead code - Condition is always FALSE: ${varName}_${version}=${constants[varKey]} ${operator} ${value}`);
            line = `if (false) { // DEAD CODE: ${leftVal} ${operator} ${rightVal} is FALSE`;
          } else {
            explanation.push(`Constant condition - Always TRUE: ${varName}_${version}=${constants[varKey]} ${operator} ${value}`);
            line = `if (true) { // Optimized: ${leftVal} ${operator} ${rightVal} is TRUE`;
          }
        }
      }
      // For more complex conditions, try to analyze them
      else if (ifMatch.length >= 2) {
        const condition = ifMatch[1];
        // Try to parse and evaluate the condition
        const condParts = condition.match(/([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)/);
        if (condParts) {
          const [, varName, version, operator, value] = condParts;
          const varKey = `${varName}_${version}`;
          
          if (constants[varKey]) {
            // Evaluate the condition statically
            const leftVal = parseInt(constants[varKey]);
            const rightVal = parseInt(value);
            let result = false;
            
            switch (operator) {
              case '==': result = leftVal === rightVal; break;
              case '!=': result = leftVal !== rightVal; break;
              case '>': result = leftVal > rightVal; break;
              case '<': result = leftVal < rightVal; break;
              case '>=': result = leftVal >= rightVal; break;
              case '<=': result = leftVal <= rightVal; break;
            }
            
            if (!result) {
              inDeadCode = true;
              explanation.push(`Dead code - Condition is always FALSE: ${varName}_${version}=${constants[varKey]} ${operator} ${value}`);
              line = `if (false) { // DEAD CODE: ${leftVal} ${operator} ${rightVal} is FALSE`;
            } else {
              explanation.push(`Constant condition - Always TRUE: ${varName}_${version}=${constants[varKey]} ${operator} ${value}`);
              line = `if (true) { // Optimized: ${leftVal} ${operator} ${rightVal} is TRUE`;
            }
          }
        }
      }
    }
    
    // Handle variable assignments with constant values and propagation
    const assignMatch = line.match(/^([a-zA-Z0-9_]+)_(\d+)\s*:=\s*(.+);$/);
    if (assignMatch && !inDeadCode) {
      const [, varName, version, expression] = assignMatch;
      
      // Check if we can optimize using constant propagation
      let optimizedExpr = expression;
      for (const [constVar, constVal] of Object.entries(constants)) {
        const regex = new RegExp(`\\b${constVar}\\b`, 'g');
        if (regex.test(optimizedExpr)) {
          optimizedExpr = optimizedExpr.replace(regex, constVal);
          explanation.push(`Constant propagation: ${constVar} → ${constVal}`);
        }
      }
      
      // Check if the right side is now a constant
      const constExprMatch = optimizedExpr.match(/^\s*(\d+)\s*$/);
      if (constExprMatch) {
        constants[`${varName}_${version}`] = constExprMatch[1];
        explanation.push(`Constant folding: ${varName}_${version} = ${constExprMatch[1]}`);
      }
      
      // Check for common subexpression elimination
      const normalizedExpr = optimizedExpr.replace(/\s+/g, '');
      if (expressions[normalizedExpr] && expressions[normalizedExpr].targets.length > 1) {
        explanation.push(`Common subexpression: ${normalizedExpr} used multiple times`);
      }
      
      // Update the line with optimized expression if it changed
      if (optimizedExpr !== expression) {
        line = `${varName}_${version} := ${optimizedExpr};`;
      }
    }
    
    // Check for assertions with constants
    const assertMatch = line.match(/^assert\(([^)]+)\);$/);
    if (assertMatch) {
      const assertion = assertMatch[1];
      // Check for comparisons like x_0 == 2
      const comparisonMatch = assertion.match(/([a-zA-Z0-9_]+)_(\d+)\s*(==|!=|>|<|>=|<=)\s*(\d+)/);
      
      if (comparisonMatch) {
        const [, varName, version, operator, value] = comparisonMatch;
        const varKey = `${varName}_${version}`;
        
        if (constants[varKey]) {
          // Evaluate the assertion statically
          const leftVal = parseInt(constants[varKey]);
          const rightVal = parseInt(value);
          let result = false;
          
          switch (operator) {
            case '==': result = leftVal === rightVal; break;
            case '!=': result = leftVal !== rightVal; break;
            case '>': result = leftVal > rightVal; break;
            case '<': result = leftVal < rightVal; break;
            case '>=': result = leftVal >= rightVal; break;
            case '<=': result = leftVal <= rightVal; break;
          }
          
          explanation.push(`Assertion evaluates to ${result ? 'TRUE' : 'FALSE'} with ${varName}_${version}=${constants[varKey]}`);
          line = `assert(${result ? 'true' : 'false'}); // Optimized from: ${assertion}`;
        }
      }
    }
    
    // Skip adding lines if they're in a dead code block and add a comment instead
    if (inDeadCode) {
      optimizedCode += `// DEAD CODE: ${line} - Will never execute\n`;
    } else {
      // Add the optimized line with explanatory comment
      optimizedCode += line + (explanation.length > 0 ? ` // ${explanation.join(', ')}` : '') + '\n';
    }
  }
  
  // Add a summary of optimizations performed
  optimizedCode += "\n// Optimization Summary:\n";
  optimizedCode += `// - Identified ${Object.keys(constants).length} constants for propagation\n`;
  
  const commonSubExprCount = Object.values(expressions)
                                 .filter(e => e.targets.length > 1).length;
  optimizedCode += `// - Found ${commonSubExprCount} common subexpressions\n`;
  
  if (optimizedCode.includes("DEAD CODE")) {
    optimizedCode += "// - Detected and marked dead code sections\n";
  }
  
  return optimizedCode;
} 