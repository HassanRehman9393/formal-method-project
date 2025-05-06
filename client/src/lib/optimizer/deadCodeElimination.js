/**
 * Dead Code Elimination Optimization
 * 
 * Identifies and removes code that has no effect on the program's output
 */

import { DataFlowAnalysis, DataFlowDirection, JoinOperation, LiveVariableAnalysis } from './dataFlowAnalysis.js';
import { buildSSAGraph } from './ssaGraph.js';

/**
 * Create a default SSA program for error handling
 * @returns {object} Default SSA program
 */
function createDefaultSSA() {
  return {
    blocks: [{
      label: 'entry',
      instructions: [],
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
      message: 'Generated fallback SSA structure for dead code elimination'
    }
  };
}

/**
 * Create a default SSA program structure, preserving metadata from original
 * @param {object} original - Original program (possibly invalid)
 * @returns {object} A minimal valid SSA program
 */
function createDefaultSSAFromProgram(original) {
  const defaultProgram = createDefaultSSA();
  
  // Preserve any metadata or properties from the original that are valid
  if (original) {
    if (original.metadata && typeof original.metadata === 'object') {
      defaultProgram.metadata = {
        ...defaultProgram.metadata,
        ...original.metadata,
        preservedFromOriginal: true
      };
    }
    
    // Preserve other top-level properties if they exist
    const validProperties = ['entryBlock', 'exitBlock', 'variables', 'constants', 'ast'];
    for (const prop of validProperties) {
      if (original[prop] !== undefined) {
        defaultProgram[prop] = original[prop];
      }
    }
  }
  
  return defaultProgram;
}

/**
 * Check if an expression might have side effects
 * @param {object} expr - Expression to check 
 * @returns {boolean} True if the expression might have side effects
 */
function hasSideEffects(expr) {
  if (!expr) return false;
  
  // Function calls may have side effects
  if (expr.type === 'CallExpression') {
    return true;
  }
  
  // Check if the expression contains any subexpressions with side effects
  if (expr.left) {
    if (hasSideEffects(expr.left)) return true;
  }
  
  if (expr.right) {
    if (hasSideEffects(expr.right)) return true;
  }
  
  if (expr.condition) {
    if (hasSideEffects(expr.condition)) return true;
  }
  
  if (expr.consequent) {
    if (hasSideEffects(expr.consequent)) return true;
  }
  
  if (expr.alternate) {
    if (hasSideEffects(expr.alternate)) return true;
  }
  
  return false;
}

/**
 * Eliminate dead code from an SSA program
 * @param {object} ssaProgram - The SSA program to optimize
 * @returns {object} Optimized SSA program
 */
export function eliminateDeadCode(ssaProgram) {
  // Validate input program structure
  if (!ssaProgram) {
    console.warn('DeadCodeElimination: Null or undefined program provided');
    return createDefaultSSA();
  }

  if (!ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
    console.warn('DeadCodeElimination: Program has no blocks array');
    return createDefaultSSAFromProgram(ssaProgram);
  }
  
  try {
    // Create a deep clone to avoid modifying the original
    const optimizedProgram = JSON.parse(JSON.stringify(ssaProgram));
    
    // Build SSA graph
    const graph = buildSSAGraph(optimizedProgram);
    
    // Run live variables analysis
    const analysis = new LiveVariableAnalysis();
    const { results } = analysis.analyze(graph);
    
    // Track if any optimizations were applied
    let optimizationsApplied = false;
    let instructionsRemoved = 0;
    
    // Apply the results to create an optimized program
    for (let i = 0; i < optimizedProgram.blocks.length; i++) {
      const block = optimizedProgram.blocks[i];
      if (!block) continue;
      
      const liveVars = results.get(block.label) || new Set();
      
      // Remove dead instructions
      const originalLength = block.instructions.length;
      block.instructions = block.instructions.filter(instr => {
        if (!instr) return false;
        
        if (instr.type === 'Assignment') {
          // Keep if target is live or has side effects
          const isLive = liveVars.has(instr.target) || hasSideEffects(instr.value);
          if (!isLive) {
            instructionsRemoved++;
            return false;
          }
        }
        return true;
      });
      
      if (block.instructions.length < originalLength) {
        optimizationsApplied = true;
        block.optimized = true;
        block.optimizationType = 'DeadCodeElimination';
      }
    }
    
    // Add metadata to indicate if optimizations were applied
    optimizedProgram.metadata = {
      ...optimizedProgram.metadata,
      deadCodeEliminationApplied: optimizationsApplied,
      instructionsRemoved
    };
    
    return optimizedProgram;
  } catch (error) {
    console.error('Error in dead code elimination:', error);
    return ssaProgram;
  }
}

// Add alias for imported name consistency
export const deadCodeElimination = eliminateDeadCode;
