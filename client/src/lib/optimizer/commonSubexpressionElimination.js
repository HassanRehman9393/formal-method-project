/**
 * Common Subexpression Elimination Optimization
 * 
 * Identifies and eliminates redundant computations in an SSA program
 */

import { buildSSAGraph } from './ssaGraph.js';
import { AvailableExpressionsAnalysis } from './dataFlowAnalysis.js';

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
 * Convert an expression to a unique key for comparison
 * @param {object} expr - Expression to convert
 * @returns {string|null} Unique key or null if not supported
 */
function expressionToKey(expr) {
  if (!expr) return null;
  
  // Only handle certain expression types
  if (expr.type === 'BinaryExpression') {
    // Create a deterministic key for binary expressions
    return `${JSON.stringify(expr.left)}-${expr.operator}-${JSON.stringify(expr.right)}`;
  }
  
  // Could extend to handle other expression types here
  
  return null;
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
  
  // Create a deep clone to avoid modifying the original
  const optimizedProgram = JSON.parse(JSON.stringify(ssaProgram));
  
  // Build SSA graph
  const graph = buildSSAGraph(optimizedProgram);
  
  // Run available expressions analysis
  const analysis = new AvailableExpressionsAnalysis();
  const { results } = analysis.analyze(graph);
  
  // Track if any optimizations were applied
  let optimizationsApplied = false;
  let expressionsEliminated = 0;
  
  // Apply the results to create an optimized program
  for (let i = 0; i < optimizedProgram.blocks.length; i++) {
    const block = optimizedProgram.blocks[i];
    if (!block) continue;
    
    const availableExpr = results.get(block.label) || new Map();
    
    // Map expressions to variables that hold them
    const exprToVar = new Map();
    
    // Process instructions to eliminate common subexpressions
    for (let j = 0; j < block.instructions.length; j++) {
      const instr = block.instructions[j];
      if (!instr) continue;
      
      if (instr.type === 'Assignment') {
        // Skip assignments to array elements for now
        if (instr.target.includes('[')) continue;
        
        // Generate a key for the expression
        const exprKey = expressionToKey(instr.value);
        
        // If this expression is already computed, reuse its result
        if (exprKey && exprToVar.has(exprKey)) {
          const existingVar = exprToVar.get(exprKey);
          
          block.instructions[j] = {
            ...instr,
            originalValue: JSON.parse(JSON.stringify(instr.value)),
            value: { 
              type: 'Identifier',
              name: existingVar
            },
            optimized: true,
            optimizationType: 'CommonSubexpressionElimination'
          };
          
          optimizationsApplied = true;
          expressionsEliminated++;
        } else if (exprKey) {
          // Register this computation for future reuse
          exprToVar.set(exprKey, instr.target);
        }
      }
    }
  }
  
  // Add metadata to indicate if optimizations were applied
  optimizedProgram.metadata = {
    ...optimizedProgram.metadata,
    commonSubexpressionEliminationApplied: optimizationsApplied,
    expressionsEliminated
  };
  
  return optimizedProgram;
}

// Export alias for compatibility with imported name
export const commonSubexpressionElimination = eliminateCommonSubexpressions;

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


