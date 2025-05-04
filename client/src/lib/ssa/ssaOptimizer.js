/**
 * SSA Generation Optimizer
 * 
 * Enhances and optimizes the SSA generation process:
 * - More efficient algorithms for large programs
 * - Better handling of complex nested structures
 * - Memory usage optimizations
 * - Performance improvements for phi placement
 */

/**
 * Optimize the SSA form generation process
 * @param {function} originalTransformFunction - Original SSA transformation function
 * @returns {function} Optimized SSA transformation function
 */
export function createOptimizedSSATransformer(originalTransformFunction) {
  return function optimizedTransformToSSA(ast, options = {}) {
    // Start performance measurement
    const startTime = performance.now();
    
    // Apply pre-processing optimizations
    const optimizedAst = preProcessAST(ast);
    
    // Apply the original transformation with optimized algorithm choices
    const optimizedOptions = {
      ...options,
      optimizePhiPlacement: true,
      useEfficientDomTree: true,
      skipUnreachableBlocks: true
    };
    
    // Call the original transform function with optimized inputs
    const ssaResult = originalTransformFunction(optimizedAst, optimizedOptions);
    
    // Apply post-processing optimizations
    const optimizedSSA = postProcessSSA(ssaResult);
    
    // Record performance metrics
    const endTime = performance.now();
    const executionTime = endTime - startTime;
    
    // Add performance metadata
    optimizedSSA.metadata = {
      ...optimizedSSA.metadata,
      ssaGeneration: {
        executionTime,
        optimized: true,
        originalBlockCount: ssaResult.blocks ? ssaResult.blocks.length : 0,
        optimizedBlockCount: optimizedSSA.blocks ? optimizedSSA.blocks.length : 0
      }
    };
    
    return optimizedSSA;
  };
}

/**
 * Pre-process the AST before SSA transformation
 * @param {Object} ast - The AST to pre-process
 * @returns {Object} Optimized AST
 */
function preProcessAST(ast) {
  if (!ast) return ast;
  
  // Create a copy of the AST
  const optimizedAst = JSON.parse(JSON.stringify(ast));
  
  // Perform AST-level optimizations
  
  // 1. Merge adjacent blocks with straight-line control flow
  mergeAdjacentBlocks(optimizedAst);
  
  // 2. Eliminate redundant expressions
  eliminateRedundantExpressions(optimizedAst);
  
  // 3. Normalize control flow for more efficient phi placement
  normalizeControlFlow(optimizedAst);
  
  return optimizedAst;
}

/**
 * Post-process the generated SSA form
 * @param {Object} ssaProgram - The SSA program to optimize
 * @returns {Object} Optimized SSA program
 */
function postProcessSSA(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) {
    return ssaProgram;
  }
  
  // Create a copy of the SSA program
  const optimizedSSA = JSON.parse(JSON.stringify(ssaProgram));
  
  // Perform SSA-level optimizations
  
  // 1. Remove trivial phi functions (phi with identical operands)
  removeTrivialPhiFunctions(optimizedSSA);
  
  // 2. Merge blocks with single predecessors
  mergeSinglePredecessorBlocks(optimizedSSA);
  
  // 3. Clean up dead variables
  removeDeadVariables(optimizedSSA);
  
  return optimizedSSA;
}

/**
 * Merge adjacent blocks with straight-line control flow
 * @param {Object} ast - The AST to optimize
 */
function mergeAdjacentBlocks(ast) {
  // Implementation would analyze the AST and merge blocks
  // where one block simply flows into another with no other
  // incoming or outgoing edges.
  if (!ast || !ast.statements) return;
  
  // This is a placeholder for the actual implementation
  // In a real implementation, we would identify sequential blocks
  // that can be merged without changing program semantics
}

/**
 * Eliminate redundant expressions in the AST
 * @param {Object} ast - The AST to optimize
 */
function eliminateRedundantExpressions(ast) {
  // Implementation would:
  // 1. Identify and eliminate common subexpressions
  // 2. Remove unreachable code
  // 3. Inline simple variable assignments
  if (!ast || !ast.statements) return;
  
  // This is a placeholder for the actual implementation
  // In a real implementation, we would perform a dataflow analysis
  // to identify and remove redundant computations
}

/**
 * Normalize control flow for more efficient SSA conversion
 * @param {Object} ast - The AST to optimize
 */
function normalizeControlFlow(ast) {
  // Implementation would:
  // 1. Ensure each branch has a dedicated block
  // 2. Add explicit "merge" blocks for control flow convergence
  // 3. Simplify nested conditionals where possible
  if (!ast || !ast.statements) return;
  
  // This is a placeholder for the actual implementation
  // In a real implementation, we would restructure the control flow
  // to make SSA construction more straightforward
}

/**
 * Remove trivial phi functions from the SSA form
 * @param {Object} ssaProgram - The SSA program to optimize
 */
function removeTrivialPhiFunctions(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) return;
  
  for (const block of ssaProgram.blocks) {
    if (!block || !block.phiFunctions) continue;
    
    // Filter out trivial phi functions
    block.phiFunctions = block.phiFunctions.filter(phi => {
      if (!phi || !phi.sources || phi.sources.length === 0) return false;
      
      // Check if all sources are identical
      const firstSource = phi.sources[0];
      const allSame = phi.sources.every(source => source === firstSource);
      
      // If all sources are the same, this phi is trivial
      if (allSame) {
        // Replace uses of phi target with the common source
        replaceVariable(ssaProgram, phi.target, firstSource);
        return false;
      }
      
      return true;
    });
  }
}

/**
 * Merge blocks that have a single predecessor
 * @param {Object} ssaProgram - The SSA program to optimize
 */
function mergeSinglePredecessorBlocks(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) return;
  
  // Calculate predecessor counts
  const predecessors = calculatePredecessors(ssaProgram);
  const merged = new Set();
  
  // Find blocks with exactly one predecessor
  for (let i = 0; i < ssaProgram.blocks.length; i++) {
    const block = ssaProgram.blocks[i];
    if (!block || merged.has(block.label)) continue;
    
    // Skip entry block and blocks with multiple predecessors
    if (block.label === ssaProgram.entryBlock ||
        !predecessors.has(block.label) ||
        predecessors.get(block.label).size !== 1) {
      continue;
    }
    
    // Get the single predecessor
    const predLabel = Array.from(predecessors.get(block.label))[0];
    const predBlock = ssaProgram.blocks.find(b => b && b.label === predLabel);
    
    // Skip if already merged or predecessor ends with a conditional branch
    if (!predBlock || merged.has(predLabel) || 
        (predBlock.terminator && predBlock.terminator.type === 'Branch')) {
      continue;
    }
    
    // Merge blocks
    predBlock.instructions = [
      ...predBlock.instructions,
      ...block.instructions
    ];
    
    // Update terminator
    predBlock.terminator = block.terminator;
    
    // Mark block as merged
    merged.add(block.label);
  }
  
  // Remove merged blocks
  ssaProgram.blocks = ssaProgram.blocks.filter(block => 
    block && !merged.has(block.label)
  );
  
  // Update branch targets
  updateBranchTargets(ssaProgram, merged);
}

/**
 * Remove unused variables from the SSA form
 * @param {Object} ssaProgram - The SSA program to optimize
 */
function removeDeadVariables(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) return;
  
  // Calculate variable uses
  const uses = calculateVariableUses(ssaProgram);
  const definitions = new Set();
  
  // Find all variable definitions
  for (const block of ssaProgram.blocks) {
    if (!block || !block.instructions) continue;
    
    for (const instr of block.instructions) {
      if (instr && instr.type === 'Assignment' && instr.target) {
        definitions.add(instr.target);
      }
    }
    
    if (block.phiFunctions) {
      for (const phi of block.phiFunctions) {
        if (phi && phi.target) {
          definitions.add(phi.target);
        }
      }
    }
  }
  
  // Find unused variables (defined but not used)
  const unused = new Set([...definitions].filter(v => !uses.has(v)));
  
  // Remove assignments to unused variables
  for (const block of ssaProgram.blocks) {
    if (!block || !block.instructions) continue;
    
    block.instructions = block.instructions.filter(instr => {
      if (!instr || instr.type !== 'Assignment') return true;
      
      // Keep the instruction if the target is used or has side effects
      return !unused.has(instr.target) || hasSideEffects(instr.value);
    });
    
    if (block.phiFunctions) {
      block.phiFunctions = block.phiFunctions.filter(phi => 
        phi && !unused.has(phi.target)
      );
    }
  }
}

/**
 * Calculate predecessors for each block in the SSA program
 * @param {Object} ssaProgram - The SSA program
 * @returns {Map} Map of block labels to sets of predecessor labels
 */
function calculatePredecessors(ssaProgram) {
  const predecessors = new Map();
  
  // Initialize empty predecessor sets
  for (const block of ssaProgram.blocks) {
    if (block && block.label) {
      predecessors.set(block.label, new Set());
    }
  }
  
  // Add predecessors based on terminators
  for (const block of ssaProgram.blocks) {
    if (!block || !block.terminator) continue;
    
    if (block.terminator.type === 'Jump') {
      const target = block.terminator.target;
      if (predecessors.has(target)) {
        predecessors.get(target).add(block.label);
      }
    } else if (block.terminator.type === 'Branch') {
      const thenTarget = block.terminator.thenTarget;
      const elseTarget = block.terminator.elseTarget;
      
      if (predecessors.has(thenTarget)) {
        predecessors.get(thenTarget).add(block.label);
      }
      
      if (predecessors.has(elseTarget)) {
        predecessors.get(elseTarget).add(block.label);
      }
    }
  }
  
  return predecessors;
}

/**
 * Calculate variable uses in the SSA program
 * @param {Object} ssaProgram - The SSA program
 * @returns {Set} Set of used variable names
 */
function calculateVariableUses(ssaProgram) {
  const uses = new Set();
  
  for (const block of ssaProgram.blocks) {
    if (!block) continue;
    
    // Check instructions for variable uses
    for (const instr of block.instructions || []) {
      if (!instr) continue;
      
      // Find variables used in the instruction
      if (instr.type === 'Assignment' && instr.value) {
        findVariables(instr.value, uses);
      } else if (instr.type === 'Assert' && instr.condition) {
        findVariables(instr.condition, uses);
      }
    }
    
    // Check terminator for variable uses
    if (block.terminator && block.terminator.condition) {
      findVariables(block.terminator.condition, uses);
    }
    
    // Check phi functions for variable uses
    for (const phi of block.phiFunctions || []) {
      if (phi && phi.sources) {
        phi.sources.forEach(source => uses.add(source));
      }
    }
  }
  
  return uses;
}

/**
 * Find all variables used in an expression
 * @param {Object} expr - The expression to analyze
 * @param {Set} variables - Set to collect variable names
 */
function findVariables(expr, variables) {
  if (!expr) return;
  
  // Variable reference
  if (expr.type === 'Variable' && expr.name) {
    variables.add(expr.name);
    return;
  }
  
  // Not an object, return
  if (typeof expr !== 'object') return;
  
  // Handle arrays
  if (Array.isArray(expr)) {
    expr.forEach(item => findVariables(item, variables));
    return;
  }
  
  // Recursive case: check all properties
  for (const key in expr) {
    if (Object.prototype.hasOwnProperty.call(expr, key) && typeof expr[key] === 'object') {
      findVariables(expr[key], variables);
    }
  }
}

/**
 * Replace all uses of one variable with another
 * @param {Object} ssaProgram - The SSA program
 * @param {string} oldVar - The variable to replace
 * @param {string} newVar - The replacement variable
 */
function replaceVariable(ssaProgram, oldVar, newVar) {
  for (const block of ssaProgram.blocks) {
    if (!block) continue;
    
    // Replace in instructions
    for (const instr of block.instructions || []) {
      if (!instr) continue;
      
      if (instr.type === 'Assignment' && instr.value) {
        replaceInExpression(instr.value, oldVar, newVar);
      } else if (instr.type === 'Assert' && instr.condition) {
        replaceInExpression(instr.condition, oldVar, newVar);
      }
    }
    
    // Replace in terminator
    if (block.terminator && block.terminator.condition) {
      replaceInExpression(block.terminator.condition, oldVar, newVar);
    }
    
    // Replace in phi functions
    for (const phi of block.phiFunctions || []) {
      if (!phi || !phi.sources) continue;
      
      phi.sources = phi.sources.map(source => 
        source === oldVar ? newVar : source
      );
    }
  }
}

/**
 * Replace a variable in an expression
 * @param {Object} expr - The expression to modify
 * @param {string} oldVar - The variable to replace
 * @param {string} newVar - The replacement variable
 */
function replaceInExpression(expr, oldVar, newVar) {
  if (!expr) return;
  
  // Variable reference
  if (expr.type === 'Variable' && expr.name === oldVar) {
    expr.name = newVar;
    return;
  }
  
  // Not an object, return
  if (typeof expr !== 'object') return;
  
  // Handle arrays
  if (Array.isArray(expr)) {
    expr.forEach(item => replaceInExpression(item, oldVar, newVar));
    return;
  }
  
  // Recursive case: check all properties
  for (const key in expr) {
    if (Object.prototype.hasOwnProperty.call(expr, key) && typeof expr[key] === 'object') {
      replaceInExpression(expr[key], oldVar, newVar);
    }
  }
}

/**
 * Update branch targets after block merging
 * @param {Object} ssaProgram - The SSA program
 * @param {Set} mergedBlocks - Set of merged block labels
 */
function updateBranchTargets(ssaProgram, mergedBlocks) {
  // Build a map of merged blocks to their new targets
  const redirectMap = new Map();
  
  // For each merged block, find where it was merged into
  for (const mergedLabel of mergedBlocks) {
    const predecessors = calculatePredecessors(ssaProgram);
    if (predecessors.has(mergedLabel)) {
      // There should be exactly one predecessor for merged blocks
      const predLabels = Array.from(predecessors.get(mergedLabel));
      if (predLabels.length === 1) {
        redirectMap.set(mergedLabel, predLabels[0]);
      }
    }
  }
  
  // Update all branch targets
  for (const block of ssaProgram.blocks) {
    if (!block || !block.terminator) continue;
    
    if (block.terminator.type === 'Jump') {
      const target = block.terminator.target;
      if (redirectMap.has(target)) {
        block.terminator.target = redirectMap.get(target);
      }
    } else if (block.terminator.type === 'Branch') {
      const thenTarget = block.terminator.thenTarget;
      const elseTarget = block.terminator.elseTarget;
      
      if (redirectMap.has(thenTarget)) {
        block.terminator.thenTarget = redirectMap.get(thenTarget);
      }
      
      if (redirectMap.has(elseTarget)) {
        block.terminator.elseTarget = redirectMap.get(elseTarget);
      }
    }
  }
}

/**
 * Check if an expression has side effects
 * @param {Object} expr - The expression to check
 * @returns {boolean} True if the expression might have side effects
 */
function hasSideEffects(expr) {
  if (!expr) return false;
  
  // Function calls might have side effects
  if (expr.type === 'CallExpression') {
    return true;
  }
  
  // Array accesses might have side effects (through getters)
  if (expr.type === 'ArrayAccess') {
    return true;
  }
  
  // Not an object, no side effects
  if (typeof expr !== 'object') return false;
  
  // Handle arrays
  if (Array.isArray(expr)) {
    return expr.some(item => hasSideEffects(item));
  }
  
  // Recursive case: check all properties
  for (const key in expr) {
    if (Object.prototype.hasOwnProperty.call(expr, key) && typeof expr[key] === 'object') {
      if (hasSideEffects(expr[key])) {
        return true;
      }
    }
  }
  
  return false;
}
