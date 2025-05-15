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
        return `assert(${expressionToSSAString(node.expression, index)});`;
      }
      return `// Assert without expression at index ${index}`;
      
    case 'IfStatement':
      let ifCode = `if (${expressionToSSAString(node.condition, index)}) {`;
      // In a real implementation, we would process the then and else branches
      ifCode += `\n  // Then branch would be processed here\n`;
      if (node.alternate) {
        ifCode += `} else {\n  // Else branch would be processed here\n}`;
      } else {
        ifCode += `}`;
      }
      return ifCode;
      
    case 'WhileStatement':
      if (node.condition) {
        return `while (${expressionToSSAString(node.condition, index)}) {\n  // Loop body would be processed here\n}`;
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
  let optimizedCode = "// Optimized SSA code\n";
  
  // Track constant values
  const constants = {};
  
  // Apply constant propagation
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    
    // Skip comments and empty lines
    if (line.startsWith('//') || line === '') {
      optimizedCode += line + '\n';
      continue;
    }
    
    // Check for variable assignments with constant values
    const assignMatch = line.match(/^([a-zA-Z0-9_]+)_(\d+)\s*:=\s*(\d+);$/);
    if (assignMatch) {
      const [, varName, version, value] = assignMatch;
      constants[`${varName}_${version}`] = value;
    }
    
    // Replace variables with their constant values in this line
    let optimizedLine = line;
    for (const [varName, value] of Object.entries(constants)) {
      const regex = new RegExp(`\\b${varName}\\b`, 'g');
      optimizedLine = optimizedLine.replace(regex, value);
    }
    
    // Add optimized line with comment if it changed
    if (optimizedLine !== line) {
      optimizedCode += optimizedLine + ' // Optimized: constant propagation\n';
    } else {
      optimizedCode += optimizedLine + '\n';
    }
    
    // Check if we can detect dead code (very basic)
    if (optimizedLine.includes('if (0)') || optimizedLine.includes('if (false)')) {
      optimizedCode += '// Dead code eliminated: conditional is always false\n';
      // Skip the next line which would be the then block
      i++;
    } else if (optimizedLine.includes('if (1)') || optimizedLine.includes('if (true)')) {
      optimizedCode += '// Optimized: conditional is always true\n';
    }
  }
  
  return optimizedCode;
} 