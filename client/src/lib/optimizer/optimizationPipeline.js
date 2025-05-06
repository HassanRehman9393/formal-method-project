/**
 * SSA Optimization Pipeline
 * 
 * Combines multiple optimization passes into a coherent pipeline
 */

import { propagateConstants } from './constantPropagation.js';
import { eliminateDeadCode } from './deadCodeElimination.js';
import { eliminateCommonSubexpressions } from './commonSubexpressionElimination.js';

/**
 * Default optimization configuration
 */
const defaultOptimizationOptions = {
  // Control which optimizations to run
  constantPropagation: true,
  deadCodeElimination: true,
  commonSubexpressionElimination: true,
  
  // Number of optimization iterations
  iterations: 3,
  
  // Metadata to track
  trackChanges: true,
  
  // Visualization options
  enhanceVisualization: true
};

/**
 * Apply a series of optimizations to an SSA program
 * @param {object} ssaProgram - The SSA program to optimize
 * @param {object} options - Optimization options
 * @returns {object} Optimized SSA program with optimization metadata
 */
export function optimizeSSA(ssaProgram, options = {}) {
  const config = { ...defaultOptimizationOptions, ...options };
  
  // Validate and create a default structure if needed
  if (!ssaProgram || typeof ssaProgram !== 'object') {
    console.warn('OptimizationPipeline: Invalid program provided');
    return { 
      program: createDefaultSSA(),
      metadata: { 
        error: 'Invalid SSA program provided',
        optimized: false,
        iterations: 0,
        passesApplied: []
      }
    };
  }
  
  if (!ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
    console.warn('OptimizationPipeline: Program has no blocks array');
    return { 
      program: createDefaultSSAFromProgram(ssaProgram),
      metadata: { 
        error: 'Program has no blocks array',
        optimized: false,
        iterations: 0,
        passesApplied: []
      }
    };
  }
  
  // Create a deep clone to avoid modifying the original
  let currentProgram;
  try {
    currentProgram = JSON.parse(JSON.stringify(ssaProgram));
  } catch (error) {
    console.warn('OptimizationPipeline: Failed to clone program', error);
    return { 
      program: createDefaultSSAFromProgram(ssaProgram),
      metadata: { 
        error: 'Failed to clone program: ' + error.message,
        optimized: false,
        iterations: 0,
        passesApplied: []
      }
    };
  }
  
  // Initialize metadata with properly initialized arrays
  const metadata = {
    optimized: false,
    iterations: 0,
    passesApplied: [],
    changes: [],
    optimizationStats: {
      constantPropagation: 0,
      deadCodeElimination: 0,
      commonSubexpressionElimination: 0
    }
  };
  
  let changed = false;
  let iterationCount = 0;
  
  // Run optimization passes until fixed point or max iterations reached
  while (iterationCount < config.iterations) {
    changed = false;
    iterationCount++;
    
    const iterationChanges = {
      iteration: iterationCount,
      passes: []
    };
    
    // Apply constant propagation
    if (config.constantPropagation) {
      try {
        const afterConstProp = propagateConstants(currentProgram);
        
        // Check if optimization was applied - look at the metadata flag
        const constPropChanged = afterConstProp && 
            (afterConstProp.metadata?.constantPropagationApplied === true || 
             afterConstProp.metadata?.constantsPropagated > 0);
        
        if (constPropChanged) {
          changed = true;
          currentProgram = afterConstProp;
          
          // Add to the passesApplied array if not already present
          if (!metadata.passesApplied.includes('ConstantPropagation')) {
            metadata.passesApplied.push('ConstantPropagation');
          }
          
          metadata.optimizationStats.constantPropagation++;
          
          iterationChanges.passes.push({
            name: 'ConstantPropagation',
            changed: constPropChanged
          });
        }
      } catch (error) {
        console.warn('Error in constant propagation:', error);
      }
    }
    
    // Apply dead code elimination
    if (config.deadCodeElimination) {
      try {
        const afterDCE = eliminateDeadCode(currentProgram);
        
        // Check if optimization was applied - look at the metadata flag
        const dceChanged = afterDCE && 
            (afterDCE.metadata?.deadCodeEliminationApplied === true || 
             afterDCE.metadata?.instructionsRemoved > 0);
        
        if (dceChanged) {
          changed = true;
          currentProgram = afterDCE;
          
          // Add to the passesApplied array if not already present
          if (!metadata.passesApplied.includes('DeadCodeElimination')) {
            metadata.passesApplied.push('DeadCodeElimination');
          }
          
          metadata.optimizationStats.deadCodeElimination++;
          
          iterationChanges.passes.push({
            name: 'DeadCodeElimination',
            changed: dceChanged
          });
        }
      } catch (error) {
        console.warn('Error in dead code elimination:', error);
      }
    }
    
    // Apply common subexpression elimination
    if (config.commonSubexpressionElimination) {
      try {
        const afterCSE = eliminateCommonSubexpressions(currentProgram);
        
        // Check if optimization was applied - look at the metadata flag
        const cseChanged = afterCSE && 
            (afterCSE.metadata?.commonSubexpressionEliminationApplied === true || 
             afterCSE.metadata?.expressionsEliminated > 0);
        
        if (cseChanged) {
          changed = true;
          currentProgram = afterCSE;
          
          // Add to the passesApplied array if not already present
          if (!metadata.passesApplied.includes('CommonSubexpressionElimination')) {
            metadata.passesApplied.push('CommonSubexpressionElimination');
          }
          
          metadata.optimizationStats.commonSubexpressionElimination++;
          
          iterationChanges.passes.push({
            name: 'CommonSubexpressionElimination',
            changed: cseChanged
          });
        }
      } catch (error) {
        console.warn('Error in common subexpression elimination:', error);
      }
    }
    
    // Record changes for this iteration
    if (config.trackChanges && iterationChanges.passes.length > 0) {
      metadata.changes.push(iterationChanges);
    }
    
    // If nothing changed, we've reached a fixed point
    if (!changed) {
      break;
    }
  }
  
  metadata.iterations = iterationCount;
  metadata.optimized = metadata.passesApplied.length > 0;
  
  // Add information about program size before/after
  if (ssaProgram.blocks && currentProgram.blocks) {
    let originalInstructions = 0;
    let optimizedInstructions = 0;
    
    ssaProgram.blocks.forEach(block => {
      if (block && block.instructions) {
        originalInstructions += block.instructions.length;
      }
    });
    
    currentProgram.blocks.forEach(block => {
      if (block && block.instructions) {
        optimizedInstructions += block.instructions.length;
      }
    });
    
    metadata.instructionCount = {
      before: originalInstructions,
      after: optimizedInstructions,
      reduction: originalInstructions - optimizedInstructions,
      reductionPercent: originalInstructions > 0 
        ? Math.round((originalInstructions - optimizedInstructions) / originalInstructions * 100) 
        : 0
    };
  }
  
  // Add optimization metadata to the program
  currentProgram.metadata = {
    ...currentProgram.metadata,
    optimizations: metadata.passesApplied,
    optimizationStats: metadata.optimizationStats,
    optimized: metadata.optimized
  };
  
  return {
    program: currentProgram,
    metadata
  };
}

/**
 * Create a default SSA program structure
 * @returns {object} A minimal valid SSA program
 */
function createDefaultSSA() {
  // Create synthetic instructions with opportunities for different optimizations
  const instructions = [
    // Constants for propagation
    {
      type: 'Assignment',
      target: 'x',
      value: { type: 'IntegerLiteral', value: 42 },
      synthetic: true
    },
    {
      type: 'Assignment',
      target: 'y',
      value: { type: 'Variable', name: 'x' }, // Should be propagated to 42
      synthetic: true
    },
    
    // Common subexpressions
    {
      type: 'Assignment',
      target: 'expr1',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'x' },
        operator: '+',
        right: { type: 'IntegerLiteral', value: 10 }
      },
      synthetic: true
    },
    {
      type: 'Assignment',
      target: 'expr2',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'x' },
        operator: '+',
        right: { type: 'IntegerLiteral', value: 10 }
      },
      synthetic: true
    },
    
    // Dead code
    {
      type: 'Assignment',
      target: 'unused',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'x' },
        operator: '*',
        right: { type: 'IntegerLiteral', value: 2 }
      },
      synthetic: true
    },
    
    // Used value
    {
      type: 'Assignment',
      target: 'result',
      value: {
        type: 'BinaryExpression',
        left: { type: 'Variable', name: 'expr1' },
        operator: '+',
        right: { type: 'Variable', name: 'expr2' }
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
      message: 'Generated fallback SSA structure for optimization pipeline',
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
