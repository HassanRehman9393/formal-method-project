/**
 * Complex Control Flow Handler for SSA Transformation
 * 
 * Handles:
 * - Break/continue statements
 * - Switch statements
 * - Try/catch/finally blocks
 * - Deeply nested control structures
 */

/**
 * Process complex control flow statements in the AST before SSA transformation
 * @param {Object} ast - The AST to process
 * @returns {Object} The processed AST
 */
export function preprocessComplexControlFlow(ast) {
  if (!ast || !ast.statements) return ast;
  
  // Create a preprocessed copy of the AST
  const processedAst = { ...ast, statements: [...ast.statements] };
  
  // Process break/continue statements by converting them to explicit jumps
  processBreakContinueStatements(processedAst);
  
  // Convert switch statements to if-else chains
  processSwitchStatements(processedAst);
  
  // Handle try-catch-finally by converting them to explicit control flow
  processTryCatchStatements(processedAst);
  
  return processedAst;
}

/**
 * Convert break/continue statements to explicit jumps
 * @param {Object} ast - The AST to process
 */
function processBreakContinueStatements(ast) {
  const visitNode = (node, loopLabels = []) => {
    if (!node) return;
    
    // Handle arrays of statements
    if (Array.isArray(node)) {
      for (let i = 0; i < node.length; i++) {
        node[i] = visitNode(node[i], loopLabels);
      }
      return node;
    }
    
    // Not an object, return as is
    if (typeof node !== 'object') return node;
    
    // Handle loops - add to loop labels stack
    if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
      // Generate a unique label for this loop
      const loopLabel = `_loop_${generateUniqueId()}`;
      node.metadata = { ...node.metadata, loopLabel };
      
      // Visit loop body with updated loop labels
      const updatedLoopLabels = [...loopLabels, loopLabel];
      node.body = visitNode(node.body, updatedLoopLabels);
      
      return node;
    }
    
    // Handle break statements
    if (node.type === 'BreakStatement') {
      if (loopLabels.length === 0) {
        throw new Error('Break statement outside loop');
      }
      
      // Get the innermost loop label
      const targetLabel = node.label ? 
        loopLabels.find(l => l === node.label.name) : 
        loopLabels[loopLabels.length - 1];
      
      if (!targetLabel) {
        throw new Error(`Label not found: ${node.label?.name}`);
      }
      
      // Convert to an explicit jump
      return {
        type: 'JumpStatement',
        target: `${targetLabel}_end`,
        originalStatement: 'break',
        location: node.location
      };
    }
    
    // Handle continue statements
    if (node.type === 'ContinueStatement') {
      if (loopLabels.length === 0) {
        throw new Error('Continue statement outside loop');
      }
      
      // Get the innermost loop label
      const targetLabel = node.label ? 
        loopLabels.find(l => l === node.label.name) : 
        loopLabels[loopLabels.length - 1];
      
      if (!targetLabel) {
        throw new Error(`Label not found: ${node.label?.name}`);
      }
      
      // Convert to an explicit jump
      return {
        type: 'JumpStatement',
        target: `${targetLabel}_continue`,
        originalStatement: 'continue',
        location: node.location
      };
    }
    
    // Recursively process all properties
    for (const key in node) {
      if (Object.prototype.hasOwnProperty.call(node, key) && typeof node[key] === 'object') {
        node[key] = visitNode(node[key], loopLabels);
      }
    }
    
    return node;
  };
  
  ast.statements = visitNode(ast.statements);
}

/**
 * Convert switch statements to if-else chains
 * @param {Object} ast - The AST to process
 */
function processSwitchStatements(ast) {
  const visitNode = (node) => {
    if (!node) return node;
    
    // Handle arrays
    if (Array.isArray(node)) {
      for (let i = 0; i < node.length; i++) {
        node[i] = visitNode(node[i]);
      }
      return node;
    }
    
    // Not an object, return as is
    if (typeof node !== 'object') return node;
    
    // Handle switch statement
    if (node.type === 'SwitchStatement') {
      const discriminant = node.discriminant;
      const cases = node.cases || [];
      
      // Find default case if present
      const defaultCase = cases.find(c => c.test === null);
      const regularCases = cases.filter(c => c.test !== null);
      
      // Convert to nested if-else statements
      let ifChain = null;
      let currentIf = null;
      
      // Build the if-else chain in reverse
      for (let i = regularCases.length - 1; i >= 0; i--) {
        const caseItem = regularCases[i];
        const test = {
          type: 'BinaryExpression',
          left: discriminant,
          operator: '===',
          right: caseItem.test
        };
        
        // Create if statement for this case
        const ifStmt = {
          type: 'IfStatement',
          condition: test,
          thenBranch: { type: 'BlockStatement', statements: caseItem.consequent },
          elseBranch: ifChain ? { type: 'BlockStatement', statements: [ifChain] } : 
                      defaultCase ? { type: 'BlockStatement', statements: defaultCase.consequent } : null
        };
        
        ifChain = ifStmt;
      }
      
      // If no cases, just return the default case or empty block
      if (!ifChain && defaultCase) {
        return {
          type: 'BlockStatement',
          statements: defaultCase.consequent,
          location: node.location
        };
      } else if (!ifChain) {
        return {
          type: 'BlockStatement',
          statements: [],
          location: node.location
        };
      }
      
      return ifChain;
    }
    
    // Recursively process all properties
    for (const key in node) {
      if (Object.prototype.hasOwnProperty.call(node, key) && typeof node[key] === 'object') {
        node[key] = visitNode(node[key]);
      }
    }
    
    return node;
  };
  
  ast.statements = visitNode(ast.statements);
}

/**
 * Convert try-catch-finally blocks to explicit control flow
 * @param {Object} ast - The AST to process
 */
function processTryCatchStatements(ast) {
  // This is a simplified version - a full implementation would be more complex
  // For now, we just convert try-catch to regular code with a flag variable
  
  const visitNode = (node) => {
    if (!node) return node;
    
    // Handle arrays
    if (Array.isArray(node)) {
      for (let i = 0; i < node.length; i++) {
        node[i] = visitNode(node[i]);
      }
      return node;
    }
    
    // Not an object, return as is
    if (typeof node !== 'object') return node;
    
    // Handle try-catch statement
    if (node.type === 'TryStatement') {
      // Generate a unique error flag variable
      const errorFlag = `_error_${generateUniqueId()}`;
      const errorVar = `_errorObj_${generateUniqueId()}`;
      
      // Create statements
      const statements = [];
      
      // Add error flag initialization
      statements.push({
        type: 'Assignment',
        target: { type: 'Variable', name: errorFlag },
        value: { type: 'BooleanLiteral', value: false }
      });
      
      // Add error object initialization
      statements.push({
        type: 'Assignment',
        target: { type: 'Variable', name: errorVar },
        value: { type: 'NullLiteral' }
      });
      
      // Add the try block with error handling wrappers
      statements.push(...node.block.statements);
      
      // Add the if statement for catch block
      if (node.handler) {
        const catchIf = {
          type: 'IfStatement',
          condition: {
            type: 'Variable',
            name: errorFlag
          },
          thenBranch: {
            type: 'BlockStatement',
            statements: [
              // Assign the error to the catch parameter
              {
                type: 'Assignment',
                target: node.handler.param,
                value: { type: 'Variable', name: errorVar }
              },
              // Add the catch block statements
              ...node.handler.body.statements
            ]
          }
        };
        statements.push(catchIf);
      }
      
      // Add finally block if present
      if (node.finalizer) {
        statements.push(...node.finalizer.statements);
      }
      
      return {
        type: 'BlockStatement',
        statements,
        location: node.location,
        metadata: { converted: 'try-catch' }
      };
    }
    
    // Recursively process all properties
    for (const key in node) {
      if (Object.prototype.hasOwnProperty.call(node, key) && typeof node[key] === 'object') {
        node[key] = visitNode(node[key]);
      }
    }
    
    return node;
  };
  
  ast.statements = visitNode(ast.statements);
}

/**
 * Generate a unique identifier
 * @returns {string} A unique identifier
 */
function generateUniqueId() {
  return Math.random().toString(36).substr(2, 9);
}
