/**
 * Loop Handler Module
 * 
 * Provides functionality for detecting and unrolling loops in ASTs
 */

/**
 * Detects loops in an AST and returns information about them
 * @param {object} ast - The AST to analyze
 * @returns {object[]} Array of loop information objects
 */
export function detectLoops(ast) {
  const loops = [];
  const visitedNodes = new Set();
  
  // Traverse the AST to find loop constructs
  traverseAst(ast, node => {
    if (!node || visitedNodes.has(node)) return;
    visitedNodes.add(node);
    
    if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
      const loopInfo = {
        type: node.type,
        node: node,
        depth: calculateLoopNestingDepth(node),
        variables: collectLoopVariables(node)
      };
      
      loops.push(loopInfo);
    }
  });
  
  return loops;
}

/**
 * Calculate the nesting depth of a loop
 * @param {object} node - The loop node to analyze
 * @returns {number} The nesting depth (1 for non-nested)
 */
function calculateLoopNestingDepth(node) {
  let depth = 1;
  let currentNode = node;
  
  // Traverse up the AST to find parent loops
  while (currentNode.parent) {
    currentNode = currentNode.parent;
    if (currentNode.type === 'WhileStatement' || currentNode.type === 'ForStatement') {
      depth++;
    }
  }
  
  return depth;
}

/**
 * Collect variables that are modified within a loop
 * @param {object} loopNode - The loop node to analyze
 * @returns {Set<string>} Set of variable names
 */
function collectLoopVariables(loopNode) {
  const variables = new Set();
  
  traverseAst(loopNode.body, node => {
    if (node.type === 'AssignmentStatement' && node.target.type === 'Identifier') {
      variables.add(node.target.name);
    }
  });
  
  return variables;
}

/**
 * Traverse an AST node and its children
 * @param {object} node - The AST node to traverse
 * @param {function} callback - Function to call for each node
 */
function traverseAst(node, callback) {
  if (!node || typeof node !== 'object') return;
  
  // Call the callback for this node
  callback(node);
  
  // Special handling for different node types
  if (node.type === 'Program' && Array.isArray(node.statements)) {
    for (const stmt of node.statements) {
      if (stmt) {
        stmt.parent = node;  // Add parent reference for depth calculation
        traverseAst(stmt, callback);
      }
    }
  } else if (node.type === 'BlockStatement' && Array.isArray(node.body)) {
    for (const stmt of node.body) {
      if (stmt) {
        stmt.parent = node;
        traverseAst(stmt, callback);
      }
    }
  } else if (node.type === 'IfStatement') {
    if (node.condition) {
      node.condition.parent = node;
      traverseAst(node.condition, callback);
    }
    if (node.consequent) {
      node.consequent.parent = node;
      traverseAst(node.consequent, callback);
    }
    if (node.alternate) {
      node.alternate.parent = node;
      traverseAst(node.alternate, callback);
    }
  } else if (node.type === 'WhileStatement' || node.type === 'ForStatement') {
    if (node.condition) {
      node.condition.parent = node;
      traverseAst(node.condition, callback);
    }
    if (node.body) {
      node.body.parent = node;
      traverseAst(node.body, callback);
    }
    if (node.type === 'ForStatement') {
      if (node.init) {
        node.init.parent = node;
        traverseAst(node.init, callback);
      }
      if (node.update) {
        node.update.parent = node;
        traverseAst(node.update, callback);
      }
    }
  }
  
  // Generic traversal for other properties
  for (const key in node) {
    if (node[key] && typeof node[key] === 'object' && key !== 'parent') {
      if (Array.isArray(node[key])) {
        for (const item of node[key]) {
          if (item && typeof item === 'object') {
            item.parent = node;
            traverseAst(item, callback);
          }
        }
      } else {
        node[key].parent = node;
        traverseAst(node[key], callback);
      }
    }
  }
}

/**
 * Unroll loops in an AST based on configuration
 * @param {object} ast - The AST to transform
 * @param {object} options - Unrolling options
 * @returns {object} Transformed AST with unrolled loops
 */
export function unrollLoops(ast, options = {}) {
  if (!ast) return ast;
  
  const maxDepth = options.unrollDepth || 5; // Default unroll depth
  const unrollAll = options.unrollAll || false; // Whether to unroll all loops
  
  try {
    // Make a simplified copy instead of using deep copy with parent references
    // This avoids circular reference issues
    const transformedAst = simpleCopyAst(ast);
    
    // Process the AST to find and unroll loops
    return processNode(transformedAst, maxDepth, unrollAll);
  } catch (error) {
    console.error('Error during loop unrolling:', error);
    return ast; // Return original AST if unrolling fails
  }
}

/**
 * Simple copy of AST without maintaining parent references
 * @param {object} node - The AST node to copy
 * @returns {object} A simple copy of the AST
 */
function simpleCopyAst(node) {
  if (!node || typeof node !== 'object') return node;
  
  // Handle arrays
  if (Array.isArray(node)) {
    return node.map(item => simpleCopyAst(item));
  }
  
  // Handle objects
  const copy = {};
  for (const key in node) {
    // Skip parent references
    if (key === 'parent') continue;
    copy[key] = simpleCopyAst(node[key]);
  }
  
  return copy;
}

/**
 * Process a node in the AST to find and unroll loops
 * @param {object} node - The AST node to process
 * @param {number} maxDepth - Maximum unroll depth
 * @param {boolean} unrollAll - Whether to unroll all loops
 * @returns {object} The processed node
 */
function processNode(node, maxDepth, unrollAll) {
  if (!node || typeof node !== 'object') return node;
  
  // Handle arrays
  if (Array.isArray(node)) {
    return node.map(item => processNode(item, maxDepth, unrollAll));
  }
  
  // Unroll loops
  if (node.type === 'WhileStatement') {
    return unrollWhileLoopSimple(node, maxDepth, unrollAll);
  } else if (node.type === 'ForStatement') {
    return unrollForLoopSimple(node, maxDepth, unrollAll);
  }
  
  // Process children recursively
  const result = { ...node };
  for (const key in result) {
    if (result[key] && typeof result[key] === 'object') {
      result[key] = processNode(result[key], maxDepth, unrollAll);
    }
  }
  
  return result;
}

/**
 * Unroll a while loop (simplified version)
 * @param {object} loopNode - The while loop node
 * @param {number} maxDepth - Maximum unroll depth
 * @param {boolean} unrollAll - Whether to unroll all loops
 * @returns {object} The transformed node
 */
function unrollWhileLoopSimple(loopNode, maxDepth, unrollAll) {
  // Create a list to hold the unrolled statements
  const statements = [];
  
  // Unroll the loop maxDepth times
  for (let i = 0; i < maxDepth; i++) {
    // Add if statement to check loop condition
    statements.push({
      type: 'IfStatement',
      condition: simpleCopyAst(loopNode.condition),
      consequent: {
        type: 'BlockStatement',
        body: [
          // Copy of the loop body
          simpleCopyAst(loopNode.body)
        ]
      },
      alternate: null
    });
  }
  
  // Return as a block statement
  return {
    type: 'BlockStatement',
    body: statements
  };
}

/**
 * Unroll a for loop (simplified version)
 * @param {object} loopNode - The for loop node
 * @param {number} maxDepth - Maximum unroll depth
 * @param {boolean} unrollAll - Whether to unroll all loops
 * @returns {object} The transformed node
 */
function unrollForLoopSimple(loopNode, maxDepth, unrollAll) {
  // Create a list to hold the unrolled statements
  const statements = [];
  
  // Add initialization if present
  if (loopNode.init) {
    statements.push(simpleCopyAst(loopNode.init));
  }
  
  // Unroll the loop maxDepth times
  for (let i = 0; i < maxDepth; i++) {
    // Add if statement to check loop condition
    statements.push({
      type: 'IfStatement',
      condition: loopNode.condition ? simpleCopyAst(loopNode.condition) : { type: 'BooleanLiteral', value: true },
      consequent: {
        type: 'BlockStatement',
        body: [
          // Copy of the loop body
          simpleCopyAst(loopNode.body),
          // Update statement if present
          ...(loopNode.update ? [simpleCopyAst(loopNode.update)] : [])
        ]
      },
      alternate: null
    });
  }
  
  // Return as a block statement
  return {
    type: 'BlockStatement',
    body: statements
  };
}

/**
 * Add parent references to AST nodes
 * @param {object} node - The AST node to process
 * @param {object} parent - The parent node
 */
function addParentReferences(node, parent = null) {
  if (!node || typeof node !== 'object') return;
  
  // Set parent reference
  if (parent) {
    node.parent = parent;
  }
  
  // Process children based on node type
  if (node.type === 'Program' && Array.isArray(node.statements)) {
    for (const stmt of node.statements) {
      if (stmt) addParentReferences(stmt, node);
    }
  } else if (node.type === 'BlockStatement' && Array.isArray(node.body)) {
    for (const stmt of node.body) {
      if (stmt) addParentReferences(stmt, node);
    }
  } else {
    // Process other node properties
    for (const key in node) {
      if (node[key] && typeof node[key] === 'object' && key !== 'parent') {
        if (Array.isArray(node[key])) {
          for (const item of node[key]) {
            if (item && typeof item === 'object') {
              addParentReferences(item, node);
            }
          }
        } else {
          addParentReferences(node[key], node);
        }
      }
    }
  }
}

/**
 * Clean parent references from the AST to make it serializable
 * @param {object} node - The AST node to clean
 */
function cleanParentReferences(node) {
  if (!node || typeof node !== 'object') return;
  
  // Remove parent property
  if ('parent' in node) {
    delete node.parent;
  }
  
  // Recursively clean children
  for (const key in node) {
    if (node[key] && typeof node[key] === 'object') {
      cleanParentReferences(node[key]);
    }
  }
}

/**
 * Replace a node in its parent node
 * @param {object} oldNode - The node to replace
 * @param {object} newNode - The replacement node
 * @param {object} parentNode - The parent node
 */
function replaceNodeInParent(oldNode, newNode, parentNode) {
  if (!parentNode) return;
  
  // Handle arrays of statements
  for (const key in parentNode) {
    if (Array.isArray(parentNode[key])) {
      const index = parentNode[key].indexOf(oldNode);
      if (index !== -1) {
        parentNode[key][index] = newNode;
        return;
      }
    } else if (parentNode[key] === oldNode) {
      parentNode[key] = newNode;
      return;
    }
  }
}

/**
 * Deep copy an object without circular references
 * @param {object} obj - The object to copy
 * @returns {object} A deep copy without circular references
 */
function deepCopyWithoutCircular(obj) {
  if (!obj || typeof obj !== 'object') {
    return obj;
  }
  
  const seen = new WeakMap();
  
  function copy(o) {
    if (o === null || typeof o !== 'object') {
      return o;
    }
    
    // If we've already copied this object, return the copy
    if (seen.has(o)) {
      return seen.get(o);
    }
    
    let result;
    
    // Handle arrays
    if (Array.isArray(o)) {
      result = [];
      seen.set(o, result);
      for (const item of o) {
        result.push(copy(item));
      }
      return result;
    }
    
    // Handle objects
    result = {};
    seen.set(o, result);
    
    for (const key in o) {
      // Skip parent references to avoid cycles
      if (key === 'parent') {
        continue;
      }
      result[key] = copy(o[key]);
    }
    
    return result;
  }
  
  return copy(obj);
}

/**
 * Analyze loop bounds to determine if it can be fully unrolled
 * @param {object} loopNode - The loop node to analyze
 * @returns {object} Analysis result with iterations count if determinable
 */
function analyzeLoopBounds(loopNode) {
  // This is a simplified version that looks for common loop patterns
  // A real implementation would use more sophisticated static analysis
  
  // Default result: can't determine statically
  const result = {
    isDeterminable: false,
    iterations: Infinity
  };
  
  // Simple case: while(i < constant) with i++ in the loop body
  try {
    if (loopNode.condition && 
        loopNode.condition.type === 'BinaryExpression' && 
        ['<', '<='].includes(loopNode.condition.operator)) {
      
      // Get loop counter variable name
      const counterVar = loopNode.condition.left.type === 'Identifier' ? 
        loopNode.condition.left.name : null;
      
      // Get loop bound value
      const boundValue = loopNode.condition.right.type === 'IntegerLiteral' ? 
        loopNode.condition.right.value : null;
      
      if (counterVar && typeof boundValue === 'number') {
        // Look for increment of the counter variable in the loop body
        const increment = findIncrementInBody(loopNode.body, counterVar);
        
        if (increment) {
          // Initial value of the counter variable
          const initialValue = findInitialValue(loopNode, counterVar);
          
          if (initialValue !== null) {
            const iterations = loopNode.condition.operator === '<' ?
              Math.ceil((boundValue - initialValue) / increment) :
              Math.ceil((boundValue + 1 - initialValue) / increment);
            
            if (iterations >= 0 && iterations !== Infinity) {
              result.isDeterminable = true;
              result.iterations = iterations;
            }
          }
        }
      }
    }
  } catch (e) {
    // If any part of the analysis fails, return the default result
    console.warn('Loop bound analysis failed:', e);
  }
  
  return result;
}

/**
 * Similar to analyzeLoopBounds but for for-loops
 * @param {object} loopNode - The for loop node
 * @returns {object} Analysis result
 */
function analyzeForLoopBounds(loopNode) {
  const result = {
    isDeterminable: false,
    iterations: Infinity
  };
  
  try {
    // Check for common for loop pattern: for(i=start; i<end; i+=step)
    if (loopNode.init && loopNode.init.type === 'AssignmentStatement' &&
        loopNode.init.target.type === 'Identifier' &&
        loopNode.condition && loopNode.condition.type === 'BinaryExpression' &&
        ['<', '<='].includes(loopNode.condition.operator) &&
        loopNode.update && loopNode.update.type === 'AssignmentStatement') {
      
      // Get counter variable name
      const counterVar = loopNode.init.target.name;
      
      // Check if condition uses the same counter variable
      if (loopNode.condition.left.type === 'Identifier' && 
          loopNode.condition.left.name === counterVar) {
        
        // Get initial value
        const initialValue = loopNode.init.value.type === 'IntegerLiteral' ?
          loopNode.init.value.value : null;
        
        // Get bound value
        const boundValue = loopNode.condition.right.type === 'IntegerLiteral' ?
          loopNode.condition.right.value : null;
        
        // Get increment value
        let increment = 1;
        if (loopNode.update.value.type === 'BinaryExpression' && 
            loopNode.update.value.operator === '+') {
          increment = loopNode.update.value.right.type === 'IntegerLiteral' ?
            loopNode.update.value.right.value : 1;
        }
        
        if (initialValue !== null && boundValue !== null && increment > 0) {
          const iterations = loopNode.condition.operator === '<' ?
            Math.ceil((boundValue - initialValue) / increment) :
            Math.ceil((boundValue + 1 - initialValue) / increment);
          
          if (iterations >= 0 && iterations !== Infinity) {
            result.isDeterminable = true;
            result.iterations = iterations;
          }
        }
      }
    }
  } catch (e) {
    console.warn('For loop bound analysis failed:', e);
  }
  
  return result;
}

/**
 * Find initial value of a variable before a loop
 * @param {object} loopNode - The loop node
 * @param {string} varName - Variable name to look for
 * @returns {number|null} Initial value if found, null otherwise
 */
function findInitialValue(loopNode, varName) {
  // Simple implementation to find a nearby assignment
  // A real implementation would use proper scope analysis
  let currentNode = loopNode;
  
  while (currentNode.parent) {
    currentNode = currentNode.parent;
    
    // Check if parent contains statements
    if (currentNode.type === 'Program' && Array.isArray(currentNode.statements)) {
      for (const stmt of currentNode.statements) {
        if (stmt.type === 'AssignmentStatement' && 
            stmt.target.type === 'Identifier' &&
            stmt.target.name === varName &&
            stmt.value.type === 'IntegerLiteral') {
          return stmt.value.value;
        }
      }
    } else if (currentNode.type === 'BlockStatement' && Array.isArray(currentNode.body)) {
      for (const stmt of currentNode.body) {
        if (stmt.type === 'AssignmentStatement' && 
            stmt.target.type === 'Identifier' &&
            stmt.target.name === varName &&
            stmt.value.type === 'IntegerLiteral') {
          return stmt.value.value;
        }
      }
    }
  }
  
  return null;
}

/**
 * Find increment value in loop body
 * @param {object} body - Loop body node
 * @param {string} varName - Variable name to look for
 * @returns {number|null} Increment value if found, null otherwise
 */
function findIncrementInBody(body, varName) {
  if (!body) return null;
  
  let statements = [];
  if (body.type === 'BlockStatement' && Array.isArray(body.body)) {
    statements = body.body;
  } else {
    statements = [body];
  }
  
  // Look for i++ or i += constant
  for (const stmt of statements) {
    if (stmt.type === 'AssignmentStatement' && 
        stmt.target.type === 'Identifier' &&
        stmt.target.name === varName) {
      
      if (stmt.value.type === 'BinaryExpression' && 
          stmt.value.operator === '+' && 
          stmt.value.left.type === 'Identifier' && 
          stmt.value.left.name === varName) {
        
        if (stmt.value.right.type === 'IntegerLiteral') {
          return stmt.value.right.value;
        }
      }
    }
  }
  
  return null;
}
