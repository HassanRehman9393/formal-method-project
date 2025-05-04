/**
 * Optimization Visualization Helper
 * 
 * Enhances optimized SSA with visualization metadata
 */

/**
 * Colors for visualization
 */
export const OptimizationColors = {
  CONSTANT_PROPAGATION: '#4ade80', // Green for constant propagation
  DEAD_CODE_ELIMINATION: '#fb7185', // Red for deleted code
  COMMON_SUBEXPRESSION: '#60a5fa', // Blue for CSE
  ORIGINAL_CODE: '#94a3b8',        // Gray for original code
  OPTIMIZED_CODE: '#c084fc'        // Purple for generic optimized code
};

/**
 * Add visualization metadata to optimized SSA program
 * @param {object} originalProgram - Original SSA program
 * @param {object} optimizedProgram - Optimized SSA program
 * @param {object} metadata - Optimization metadata
 * @returns {object} Program with visualization metadata
 */
export function addVisualizationMetadata(originalProgram, optimizedProgram, metadata) {
  // Validate inputs
  if (!optimizedProgram || !optimizedProgram.blocks) {
    console.warn('Visualization: Invalid optimized program');
    return optimizedProgram;
  }
  
  if (!originalProgram || !originalProgram.blocks) {
    console.warn('Visualization: Invalid original program');
    return optimizedProgram;
  }
  
  // Clone the optimized program to avoid modifying original
  let visualProgram;
  try {
    visualProgram = JSON.parse(JSON.stringify(optimizedProgram));
  } catch (error) {
    console.warn('Visualization: Failed to clone program', error);
    return optimizedProgram;
  }
  
  // Track eliminated instructions
  const eliminatedInstructions = findEliminatedInstructions(originalProgram, optimizedProgram);
  
  // Process each block to identify differences
  for (let i = 0; i < visualProgram.blocks.length; i++) {
    const block = visualProgram.blocks[i];
    if (!block) continue;
    
    // Enhance instructions with visualization metadata
    if (block.instructions) {
      for (let j = 0; j < block.instructions.length; j++) {
        const instr = block.instructions[j];
        if (!instr) continue;
        
        // Check if instruction was optimized
        if (instr.optimized) {
          // Add visualization class based on optimization type
          instr.visualClass = determineVisualizationClass(instr);
          
          // Add specific description based on optimization
          if (instr.originalValue) {
            instr.visualTooltip = `Optimized from: ${formatExpression(instr.originalValue)}`;
            
            // Make sure optimized flag is set properly
            instr.optimized = true;
          }
        }
      }
    }
    
    // Handle terminator optimization visualization
    if (block.terminator && block.terminator.optimized) {
      block.terminator.visualClass = OptimizationColors.CONSTANT_PROPAGATION;
      
      if (block.terminator.originalCondition) {
        block.terminator.visualTooltip = 
          `Optimized from: ${formatExpression(block.terminator.originalCondition)}`;
      }
    }
  }
  
  // Add eliminated instructions for visualization
  visualProgram.eliminatedInstructions = eliminatedInstructions;
  
  // Add overall visualization metadata
  visualProgram.visualization = {
    passesApplied: metadata.passesApplied || [],
    optimized: metadata.optimized || false,
    changes: metadata.changes || [],
    visualEnhanced: true  // Mark as visually enhanced
  };
  
  return visualProgram;
}

/**
 * Find instructions that were eliminated during optimization
 */
function findEliminatedInstructions(originalProgram, optimizedProgram) {
  const result = new Map();
  
  if (!originalProgram || !originalProgram.blocks || 
      !optimizedProgram || !optimizedProgram.blocks) {
    return result;
  }
  
  // Create a map of optimized blocks by label
  const optimizedBlocks = new Map();
  for (const block of optimizedProgram.blocks) {
    if (block && block.label) {
      optimizedBlocks.set(block.label, block);
    }
  }
  
  // Compare original blocks with optimized blocks
  for (const originalBlock of originalProgram.blocks) {
    if (!originalBlock || !originalBlock.label) continue;
    
    const optimizedBlock = optimizedBlocks.get(originalBlock.label);
    if (!optimizedBlock) {
      // Entire block was eliminated
      result.set(originalBlock.label, originalBlock.instructions || []);
      continue;
    }
    
    // Find eliminated instructions within the block
    const eliminatedFromBlock = [];
    
    if (originalBlock.instructions && optimizedBlock.instructions) {
      // Create a set of optimized instruction targets for quick lookup
      const optimizedTargets = new Set();
      for (const instr of optimizedBlock.instructions) {
        if (instr && instr.target) {
          optimizedTargets.add(instr.target);
        }
      }
      
      // Check each original instruction to see if it was eliminated
      for (const instr of originalBlock.instructions) {
        if (instr && instr.target && !optimizedTargets.has(instr.target)) {
          eliminatedFromBlock.push({
            ...instr,
            visualClass: OptimizationColors.DEAD_CODE_ELIMINATION,
            visualTooltip: 'Eliminated dead code'
          });
        }
      }
    }
    
    if (eliminatedFromBlock.length > 0) {
      result.set(originalBlock.label, eliminatedFromBlock);
    }
  }
  
  return result;
}

/**
 * Determine visualization class based on optimization type
 * @param {object} instr - Optimized instruction
 * @returns {string} CSS class or color
 */
function determineVisualizationClass(instr) {
  if (!instr) return OptimizationColors.ORIGINAL_CODE;
  
  // Use explicit optimization type if available
  if (instr.optimizationType) {
    if (instr.optimizationType === 'constantPropagation') {
      return OptimizationColors.CONSTANT_PROPAGATION;
    } else if (instr.optimizationType === 'commonSubexpressionElimination') {
      return OptimizationColors.COMMON_SUBEXPRESSION;
    } else if (instr.optimizationType === 'deadCodeElimination') {
      return OptimizationColors.DEAD_CODE_ELIMINATION;
    }
  }
  
  // Check for specific optimization patterns
  
  // Constant propagation typically replaces variables with literals
  if (instr.value && 
      (instr.value.type === 'IntegerLiteral' || 
       instr.value.type === 'BooleanLiteral') &&
      instr.originalValue &&
      (instr.originalValue.type === 'Variable' || 
       instr.originalValue.type === 'BinaryExpression')) {
    return OptimizationColors.CONSTANT_PROPAGATION;
  }
  
  // Common subexpression elimination replaces expressions with variables
  if (instr.value && 
      instr.value.type === 'Variable' &&
      instr.originalValue &&
      (instr.originalValue.type === 'BinaryExpression' ||
       instr.originalValue.type === 'UnaryExpression')) {
    return OptimizationColors.COMMON_SUBEXPRESSION;
  }
  
  // Default for other optimizations
  return OptimizationColors.OPTIMIZED_CODE;
}

/**
 * Format an expression for display in tooltips
 * @param {object} expr - Expression to format
 * @returns {string} Formatted string
 */
function formatExpression(expr) {
  if (!expr) return 'undefined';
  
  if (typeof expr !== 'object') {
    return String(expr);
  }
  
  try {
    switch (expr.type) {
      case 'Variable':
        return expr.name || 'unnamed';
        
      case 'IntegerLiteral':
      case 'BooleanLiteral':
        return expr.value !== undefined ? String(expr.value) : 'unknown';
        
      case 'BinaryExpression':
        return `${formatExpression(expr.left)} ${expr.operator || '?'} ${formatExpression(expr.right)}`;
        
      case 'UnaryExpression':
        return `${expr.operator || ''}${formatExpression(expr.operand)}`;
        
      case 'ArrayAccess':
        return `${formatExpression(expr.array)}[${formatExpression(expr.index)}]`;
        
      default:
        return expr.type || 'unknown';
    }
  } catch (error) {
    return 'error formatting expression';
  }
}

/**
 * Generate a summary of the optimizations applied
 * @param {object} metadata - Optimization metadata
 * @returns {object} Summary information
 */
export function generateOptimizationSummary(metadata) {
  if (!metadata) {
    return {
      totalOptimizations: 0,
      byType: {
        constantPropagation: 0,
        deadCodeElimination: 0,
        commonSubexpressionElimination: 0
      },
      efficiency: 0,
      iterations: 0
    };
  }
  
  const summary = {
    totalOptimizations: 0,
    byType: {
      constantPropagation: 0,
      deadCodeElimination: 0,
      commonSubexpressionElimination: 0
    },
    efficiency: 0,
    iterations: metadata.iterations || 0
  };
  
  // Count optimizations by type
  if (metadata.passesApplied) {
    metadata.passesApplied.forEach(pass => {
      if (pass === 'constantPropagation') summary.byType.constantPropagation++;
      if (pass === 'deadCodeElimination') summary.byType.deadCodeElimination++;
      if (pass === 'commonSubexpressionElimination') summary.byType.commonSubexpressionElimination++;
    });
    
    summary.totalOptimizations = metadata.passesApplied.length;
  }
  
  // Calculate efficiency (if available)
  if (metadata.instructionCount) {
    const instructionsBefore = metadata.instructionCount.before || 0;
    const instructionsAfter = metadata.instructionCount.after || 0;
    summary.efficiency = instructionsBefore > 0 ? 
      Math.round(100 * (1 - instructionsAfter / instructionsBefore)) : 0;
  }
  
  return summary;
}
