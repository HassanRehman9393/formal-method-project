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
  deadCodeElimination: true,  // Enable by default
  commonSubexpressionElimination: true,  // Enable by default
  
  // Number of optimization iterations
  iterations: 3,  // Increase default iterations for better results
  
  // Metadata to track
  trackChanges: true
};

/**
 * Apply a series of optimizations to an SSA program
 * @param {object} ssaProgram - The SSA program to optimize
 * @param {object} options - Optimization options
 * @returns {object} Optimized SSA program with optimization metadata
 */
export function optimizeSSA(ssaProgram, options = {}) {
  const config = { ...defaultOptimizationOptions, ...options };
  
  if (!ssaProgram || !ssaProgram.blocks) {
    return { 
      program: ssaProgram,
      metadata: { 
        error: 'Invalid SSA program provided',
        optimized: false,
        iterations: 0,
        passesApplied: [] // Ensure passesApplied is initialized
      }
    };
  }
  
  // Initialize metadata with properly initialized arrays
  const metadata = {
    optimized: false,
    iterations: 0,
    passesApplied: [], // Ensure this is always an array
    changes: []
  };
  
  let currentProgram = ssaProgram;
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
      const beforeConstProp = JSON.stringify(currentProgram);
      const afterConstProp = propagateConstants(currentProgram);
      
      const constPropChanged = beforeConstProp !== JSON.stringify(afterConstProp);
      if (constPropChanged) {
        changed = true;
        currentProgram = afterConstProp;
        metadata.passesApplied.push('constantPropagation');
        
        iterationChanges.passes.push({
          name: 'constantPropagation',
          changed: constPropChanged
        });
      }
    }
    
    // Apply dead code elimination
    if (config.deadCodeElimination) {
      const beforeDCE = JSON.stringify(currentProgram);
      const afterDCE = eliminateDeadCode(currentProgram);
      
      const dceChanged = beforeDCE !== JSON.stringify(afterDCE);
      if (dceChanged) {
        changed = true;
        currentProgram = afterDCE;
        metadata.passesApplied.push('deadCodeElimination');
        
        iterationChanges.passes.push({
          name: 'deadCodeElimination',
          changed: dceChanged
        });
      }
    }
    
    // Apply common subexpression elimination
    if (config.commonSubexpressionElimination) {
      const beforeCSE = JSON.stringify(currentProgram);
      const afterCSE = eliminateCommonSubexpressions(currentProgram);
      
      const cseChanged = beforeCSE !== JSON.stringify(afterCSE);
      if (cseChanged) {
        changed = true;
        currentProgram = afterCSE;
        metadata.passesApplied.push('commonSubexpressionElimination');
        
        iterationChanges.passes.push({
          name: 'commonSubexpressionElimination',
          changed: cseChanged
        });
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
  metadata.optimized = iterationCount > 0 && metadata.passesApplied.length > 0;
  
  return {
    program: currentProgram,
    metadata
  };
}
