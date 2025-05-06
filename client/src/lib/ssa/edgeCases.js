/**
 * SSA Edge Cases Integration Module
 * 
 * This module integrates all the edge case handling components
 * and provides an API for the rest of the application.
 */

import { preprocessComplexControlFlow } from './complexControlFlow.js';
import { analyzeArrayBounds } from './arrayBoundsAnalysis.js';
import { processComplexAssertions } from './complexAssertions.js';
import { createOptimizedSSATransformer } from './ssaOptimizer.js';

/**
 * Enhance the SSA transformation to handle edge cases
 * @param {Function} originalTransformToSSA - The original SSA transformation function
 * @returns {Function} Enhanced SSA transformation function
 */
export function enhanceSSATransformer(originalTransformToSSA) {
  // Create an optimized version of the original transformer
  const optimizedTransformer = createOptimizedSSATransformer(originalTransformToSSA);
  
  /**
   * Enhanced SSA transformation with edge case handling
   * @param {Object} ast - The AST to transform
   * @param {Object} options - Transformation options
   * @returns {Object} SSA program with edge case handling
   */
  return function enhancedTransformToSSA(ast, options = {}) {
    // Merge default options
    const mergedOptions = {
      handleComplexControlFlow: true,
      analyzeArrayBounds: true,
      processComplexAssertions: true,
      optimizeSSAGeneration: true,
      ...options
    };
    
    try {
      // Start performance measurement
      const startTime = performance.now();
      
      // Phase 1: Pre-process AST to handle complex control flow
      let processedAst = ast;
      if (mergedOptions.handleComplexControlFlow) {
        processedAst = preprocessComplexControlFlow(ast);
      }
      
      // Phase 2: Use optimized SSA transformer to generate initial SSA
      const basicSSA = optimizedTransformer(processedAst, mergedOptions);
      
      // Phase 3: Post-process SSA for edge cases
      let enhancedSSA = basicSSA;
      
      // Add array bounds analysis
      if (mergedOptions.analyzeArrayBounds) {
        enhancedSSA = analyzeArrayBounds(enhancedSSA, {
          insertRuntimeChecks: mergedOptions.insertRuntimeChecks !== false,
          generateAssertions: mergedOptions.generateAssertions !== false
        });
      }
      
      // Process complex assertions
      if (mergedOptions.processComplexAssertions) {
        enhancedSSA = processComplexAssertions(enhancedSSA);
      }
      
      // Record performance metrics
      const endTime = performance.now();
      const executionTime = endTime - startTime;
      
      // Add metadata about the edge case handling
      enhancedSSA.metadata = {
        ...enhancedSSA.metadata,
        edgeCaseHandling: {
          executionTime,
          complexControlFlow: mergedOptions.handleComplexControlFlow,
          arrayBoundsAnalysis: mergedOptions.analyzeArrayBounds,
          complexAssertions: mergedOptions.processComplexAssertions,
          optimizedGeneration: mergedOptions.optimizeSSAGeneration
        }
      };
      
      return enhancedSSA;
    } catch (error) {
      console.error('Error in enhanced SSA transformation:', error);
      
      // Fallback to original transformer in case of errors
      return originalTransformToSSA(ast, options);
    }
  };
}

/**
 * Create a configuration object for SSA edge case handling
 * @param {Object} options - User configuration options
 * @returns {Object} Configuration object for SSA edge case handling
 */
export function createEdgeCaseConfig(options = {}) {
  return {
    // Control flow handling
    handleComplexControlFlow: options.handleComplexControlFlow !== false,
    
    // Array bounds handling
    analyzeArrayBounds: options.analyzeArrayBounds !== false,
    insertRuntimeChecks: options.insertRuntimeChecks !== false,
    generateAssertions: options.generateAssertions !== false,
    
    // Assertion handling
    processComplexAssertions: options.processComplexAssertions !== false,
    
    // Optimization settings
    optimizeSSAGeneration: options.optimizeSSAGeneration !== false,
    
    // Advanced options
    treatWarningsAsErrors: options.treatWarningsAsErrors || false,
    validateResults: options.validateResults !== false
  };
}

/**
 * Validate an SSA program for correctness
 * @param {Object} ssaProgram - The SSA program to validate
 * @returns {Object} Validation results with any issues found
 */
export function validateSSAProgram(ssaProgram) {
  const issues = [];
  
  if (!ssaProgram) {
    issues.push({ severity: 'error', message: 'SSA program is null or undefined' });
    return { valid: false, issues };
  }
  
  if (!ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
    issues.push({ severity: 'error', message: 'SSA program has no blocks array' });
    return { valid: false, issues };
  }
  
  // Validate blocks
  for (let i = 0; i < ssaProgram.blocks.length; i++) {
    const block = ssaProgram.blocks[i];
    
    if (!block) {
      issues.push({ 
        severity: 'error', 
        message: `Block at index ${i} is null or undefined` 
      });
      continue;
    }
    
    if (!block.label) {
      issues.push({ 
        severity: 'error', 
        message: `Block at index ${i} has no label` 
      });
    }
    
    if (!block.instructions || !Array.isArray(block.instructions)) {
      issues.push({ 
        severity: 'warning', 
        message: `Block ${block.label} has no instructions array` 
      });
    }
    
    // Validate terminator
    if (!block.terminator && i < ssaProgram.blocks.length - 1) {
      issues.push({ 
        severity: 'warning', 
        message: `Block ${block.label} has no terminator but is not the exit block` 
      });
    }
  }
  
  // Validate entry and exit blocks
  if (!ssaProgram.entryBlock) {
    issues.push({ severity: 'error', message: 'SSA program has no entry block' });
  } else if (!ssaProgram.blocks.some(b => b && b.label === ssaProgram.entryBlock)) {
    issues.push({ severity: 'error', message: `Entry block "${ssaProgram.entryBlock}" not found` });
  }
  
  if (!ssaProgram.exitBlock) {
    issues.push({ severity: 'error', message: 'SSA program has no exit block' });
  } else if (!ssaProgram.blocks.some(b => b && b.label === ssaProgram.exitBlock)) {
    issues.push({ severity: 'error', message: `Exit block "${ssaProgram.exitBlock}" not found` });
  }
  
  // Check for errors
  const hasErrors = issues.some(issue => issue.severity === 'error');
  
  return {
    valid: !hasErrors,
    issues
  };
}

/**
 * Handle edge cases in SSA transformation
 * This is a wrapper function to process edge cases in an SSA program
 * @param {Object} ssaProgram - The SSA program to process
 * @param {Object} options - Edge case handling options
 * @returns {Object} The processed SSA program
 */
export function handleEdgeCases(ssaProgram, options = {}) {
  const config = createEdgeCaseConfig(options);
  
  try {
    let processedSSA = ssaProgram;
    
    // Add array bounds analysis
    if (config.analyzeArrayBounds) {
      processedSSA = analyzeArrayBounds(processedSSA, {
        insertRuntimeChecks: config.insertRuntimeChecks,
        generateAssertions: config.generateAssertions
      });
    }
    
    // Process complex assertions
    if (config.processComplexAssertions) {
      processedSSA = processComplexAssertions(processedSSA);
    }
    
    // Validate the results if requested
    if (config.validateResults) {
      const validationResult = validateSSAProgram(processedSSA);
      
      if (!validationResult.valid && config.treatWarningsAsErrors) {
        throw new Error(`Invalid SSA program: ${validationResult.issues[0]?.message}`);
      }
      
      // Add validation results to metadata
      processedSSA.metadata = {
        ...processedSSA.metadata,
        validation: validationResult
      };
    }
    
    return processedSSA;
  } catch (error) {
    console.error('Error handling edge cases:', error);
    return ssaProgram; // Return original if error occurs
  }
}
