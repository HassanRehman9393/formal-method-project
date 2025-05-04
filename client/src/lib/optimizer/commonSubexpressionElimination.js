/**
 * Common Subexpression Elimination Optimization
 * 
 * Eliminates redundant computations
 */

/**
 * Create a hash for an expression
 * @param {object} expr - Expression to hash
 * @returns {string} Hash string
 */
function hashExpression(expr) {
  if (!expr) return 'null';
  
  if (typeof expr !== 'object') {
    return String(expr);
  }
  
  if (expr.type === 'IntegerLiteral' || expr.type === 'BooleanLiteral') {
    return `${expr.type}:${expr.value}`;
  }
  
  if (expr.type === 'Variable') {
    return `Variable:${expr.name}`;
  }
  
  if (expr.type === 'BinaryExpression') {
    return `Binary:${hashExpression(expr.left)}${expr.operator}${hashExpression(expr.right)}`;
  }
  
  if (expr.type === 'UnaryExpression') {
    return `Unary:${expr.operator}${hashExpression(expr.operand)}`;
  }
  
  // Fallback for other types
  return `${expr.type}:${JSON.stringify(expr)}`;
}

/**
 * Eliminate common subexpressions from an SSA program
 * @param {object} ssaProgram - The SSA program to optimize
 * @returns {object} Optimized SSA program
 */
export function eliminateCommonSubexpressions(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
    console.warn('CSE: Invalid SSA program provided');
    return createDefaultSSA();
  }
  
  try {
    // Create a deep clone to avoid modifying the original
    const optimizedProgram = JSON.parse(JSON.stringify(ssaProgram));
    
    // Track if any optimizations were applied
    let optimizationsApplied = false;
    let expressionsEliminated = 0;
    
    // Apply CSE block by block
    for (let blockIndex = 0; blockIndex < optimizedProgram.blocks.length; blockIndex++) {
      const block = optimizedProgram.blocks[blockIndex];
      if (!block || !block.instructions) continue;
      
      const availableExpressions = new Map();
      let blockModified = false;
      
      // First pass: record all expressions
      for (let i = 0; i < block.instructions.length; i++) {
        const instr = block.instructions[i];
        if (!instr || instr.type !== 'Assignment') continue;
        
        // Skip simple assignments and literals
        if (!instr.value || 
            instr.value.type === 'Variable' || 
            instr.value.type === 'IntegerLiteral' || 
            instr.value.type === 'BooleanLiteral') {
          continue;
        }
        
        // Hash the expression
        const hash = hashExpression(instr.value);
        
        // Add to available expressions
        availableExpressions.set(hash, {
          target: instr.target,
          value: instr.value,
          index: i
        });
      }
      
      // Second pass: replace common subexpressions
      for (let i = 0; i < block.instructions.length; i++) {
        const instr = block.instructions[i];
        if (!instr || instr.type !== 'Assignment') continue;
        
        // Skip simple assignments and literals
        if (!instr.value || 
            instr.value.type === 'Variable' || 
            instr.value.type === 'IntegerLiteral' || 
            instr.value.type === 'BooleanLiteral') {
          continue;
        }
        
        // Hash the expression
        const hash = hashExpression(instr.value);
        
        // Get the first occurrence of this expression
        const firstOccurrence = availableExpressions.get(hash);
        
        // Replace with variable if this is a later occurrence
        if (firstOccurrence && firstOccurrence.index < i && firstOccurrence.target !== instr.target) {
          // Store the original expression for visualization
          const originalValue = JSON.parse(JSON.stringify(instr.value));
          
          // Replace with a reference to the variable
          block.instructions[i] = {
            type: 'Assignment',
            target: instr.target,
            value: {
              type: 'Variable',
              name: firstOccurrence.target
            },
            optimized: true,
            originalValue: originalValue,
            optimizationType: 'commonSubexpressionElimination'
          };
          
          blockModified = true;
          expressionsEliminated++;
        }
      }
      
      if (blockModified) {
        optimizationsApplied = true;
        block.optimized = true;
        block.metadata = {
          ...block.metadata,
          commonSubexpressionElimination: {
            applied: true,
            expressionsEliminated: expressionsEliminated
          }
        };
      }
    }
    
    // Add metadata to indicate if optimizations were applied
    optimizedProgram.metadata = {
      ...optimizedProgram.metadata,
      commonSubexpressionEliminationApplied: optimizationsApplied,
      expressionsEliminated
    };
    
    return optimizedProgram;
  } catch (error) {
    console.error('CSE: Error during optimization', error);
    return ssaProgram;
  }
}

/**
 * Create a default SSA program structure with CSE opportunities
 * @returns {object} A minimal valid SSA program
 */
function createDefaultSSA() {
  // Create synthetic instructions with common subexpressions
  const instructions = [
    {
      type: 'Assignment',
      target: 'a',
      value: { type: 'IntegerLiteral', value: 5 },
      synthetic: true
    },
    {
      type: 'Assignment',
      target: 'b',
      value: { type: 'IntegerLiteral', value: 10 },
      synthetic: true
    },
    // First occurrence of a+b
    {
      type: 'Assignment',
      target: 'expr1',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'a' },
        operator: '+',
        right: { type: 'Variable', name: 'b' }
      },
      synthetic: true
    },
    // Second occurrence of a+b (common subexpression)
    {
      type: 'Assignment',
      target: 'expr2',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'a' },
        operator: '+',
        right: { type: 'Variable', name: 'b' }
      },
      synthetic: true
    },
    // Third occurrence of a+b (common subexpression)
    {
      type: 'Assignment',
      target: 'expr3',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'a' },
        operator: '+',
        right: { type: 'Variable', name: 'b' }
      },
      synthetic: true
    },
    // Result that combines expressions
    {
      type: 'Assignment',
      target: 'result',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'expr1' },
        operator: '+',
        right: {
          type: 'BinaryExpression',
          left: { type: 'Variable', name: 'expr2' },
          operator: '+',
          right: { type: 'Variable', name: 'expr3' }
        }
      },
      synthetic: true
    }
  ];
  
  return {
    blocks: [{
      label: 'entry',
      instructions,
      terminator: { type: 'Jump', target: 'exit' }
    }, {
      label: 'exit',
      instructions: [],
      terminator: null
    }],
    entryBlock: 'entry',
    exitBlock: 'exit',
    metadata: {
      synthetic: true,
      message: 'Generated fallback SSA for common subexpression elimination',
      commonSubexpressionEliminationApplied: false
    }
  };
}
