/**
 * Common Subexpression Elimination
 * 
 * Eliminates redundant expressions that have been computed before
 * and whose values haven't changed
 */

import { buildSSAGraph } from './ssaGraph.js';

/**
 * Expression hash for comparison
 * @param {object} expr - Expression to hash
 * @returns {string} Hash string
 */
function hashExpression(expr) {
  if (!expr || typeof expr !== 'object') return String(expr);
  
  if (expr.type === 'Variable') {
    return `VAR:${expr.name}`;
  }
  
  if (expr.type === 'IntegerLiteral') {
    return `INT:${expr.value}`;
  }
  
  if (expr.type === 'BooleanLiteral') {
    return `BOOL:${expr.value}`;
  }
  
  if (expr.type === 'BinaryExpression') {
    return `BIN:(${hashExpression(expr.left)})${expr.operator}(${hashExpression(expr.right)})`;
  }
  
  if (expr.type === 'UnaryExpression') {
    return `UNA:${expr.operator}(${hashExpression(expr.operand)})`;
  }
  
  if (expr.type === 'ArrayAccess') {
    return `ARR:${hashExpression(expr.array)}[${hashExpression(expr.index)}]`;
  }
  
  // Default case
  return `${expr.type}:${JSON.stringify(expr)}`;
}

/**
 * Find common subexpressions within a basic block
 * @param {object} block - SSA basic block
 * @returns {Map} Map of expression hashes to variables
 */
function findAvailableExpressions(block) {
  const availableExpressions = new Map();
  
  // Process each instruction
  for (const instr of block.instructions) {
    if (!instr || instr.type !== 'Assignment') continue;
    
    // Skip simple assignments of variables or constants
    if (instr.value.type === 'Variable' || 
        instr.value.type === 'IntegerLiteral' || 
        instr.value.type === 'BooleanLiteral') {
      continue;
    }
    
    // Hash the expression
    const hash = hashExpression(instr.value);
    
    // Store the mapping from expression to variable name
    availableExpressions.set(hash, instr.target);
  }
  
  return availableExpressions;
}

/**
 * Eliminate common subexpressions from an SSA program
 * @param {object} ssaProgram - The SSA program to optimize
 * @returns {object} Optimized SSA program
 */
export function eliminateCommonSubexpressions(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) {
    return ssaProgram; // Return unmodified program if invalid
  }
  
  // Apply CSE block by block
  const optimizedProgram = {
    ...ssaProgram,
    blocks: ssaProgram.blocks.map(block => {
      if (!block) return block;
      
      const availableExpressions = findAvailableExpressions(block);
      let modified = false;
      
      // Create optimized instructions by replacing common subexpressions
      const optimizedInstructions = [];
      
      // Process each instruction
      for (let i = 0; i < block.instructions.length; i++) {
        const instr = block.instructions[i];
        if (!instr) {
          optimizedInstructions.push(instr);
          continue;
        }
        
        if (instr.type === 'Assignment') {
          // Skip simple assignments
          if (instr.value.type === 'Variable' || 
              instr.value.type === 'IntegerLiteral' || 
              instr.value.type === 'BooleanLiteral') {
            optimizedInstructions.push(instr);
            continue;
          }
          
          // Hash the expression
          const hash = hashExpression(instr.value);
          
          // Check if this expression has already been computed
          if (availableExpressions.has(hash) && 
              availableExpressions.get(hash) !== instr.target) {
              
            const existingVar = availableExpressions.get(hash);
            
            // Replace with a simple variable assignment
            const optimizedInstr = {
              type: 'Assignment',
              target: instr.target,
              value: { type: 'Variable', name: existingVar },
              optimized: true,
              originalValue: instr.value
            };
            
            optimizedInstructions.push(optimizedInstr);
            modified = true;
          } else {
            // First occurrence of this expression
            optimizedInstructions.push(instr);
            
            // Register this expression
            availableExpressions.set(hash, instr.target);
          }
        } else {
          optimizedInstructions.push(instr);
        }
      }
      
      return {
        ...block,
        instructions: optimizedInstructions,
        optimized: modified,
        metadata: {
          ...block.metadata,
          commonSubexpressionElimination: {
            expressionsFound: availableExpressions.size,
            modified
          }
        }
      };
    })
  };
  
  return optimizedProgram;
}
