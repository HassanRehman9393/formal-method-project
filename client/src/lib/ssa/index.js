/**
 * SSA Module Entry Point
 * 
 * This file exports the enhanced SSA transformation functionality with edge case handling
 */

// Import original SSA transformer (assuming this exists)
import { transformToSSA as originalTransformToSSA } from './transformer.js';

// Import edge case enhancements
import { 
  enhanceSSATransformer, 
  createEdgeCaseConfig, 
  validateSSAProgram 
} from './edgeCases.js';

// Export individual components for direct use
export { preprocessComplexControlFlow } from './complexControlFlow.js';
export { analyzeArrayBounds } from './arrayBoundsAnalysis.js';
export { processComplexAssertions } from './complexAssertions.js';
export { createOptimizedSSATransformer } from './ssaOptimizer.js';

// Create the enhanced transformer
const enhancedTransformToSSA = enhanceSSATransformer(originalTransformToSSA);

// Export the primary functions
export {
  enhancedTransformToSSA as transformToSSA,
  createEdgeCaseConfig,
  validateSSAProgram,
  originalTransformToSSA as basicTransformToSSA
};

// Define transformation options
export const SSATransformationOptions = {
  // Loop handling
  DEFAULT_LOOP_UNROLL_DEPTH: 5,
  UNROLL_ALL_LOOPS: false,
  
  // Edge case handling
  HANDLE_COMPLEX_CONTROL_FLOW: true,
  ANALYZE_ARRAY_BOUNDS: true,
  PROCESS_COMPLEX_ASSERTIONS: true,
  OPTIMIZE_SSA_GENERATION: true,
  
  // Runtime behavior
  INSERT_RUNTIME_CHECKS: true,
  GENERATE_ASSERTIONS: true,
  TREAT_WARNINGS_AS_ERRORS: false,
  VALIDATE_RESULTS: true,
  
  // Create default options object
  createDefaultOptions(userOptions = {}) {
    return {
      unrollDepth: userOptions.unrollDepth || this.DEFAULT_LOOP_UNROLL_DEPTH,
      unrollAll: userOptions.unrollAll || this.UNROLL_ALL_LOOPS,
      
      handleComplexControlFlow: 
        userOptions.handleComplexControlFlow !== undefined ?
        userOptions.handleComplexControlFlow : this.HANDLE_COMPLEX_CONTROL_FLOW,
        
      analyzeArrayBounds:
        userOptions.analyzeArrayBounds !== undefined ?
        userOptions.analyzeArrayBounds : this.ANALYZE_ARRAY_BOUNDS,
        
      processComplexAssertions:
        userOptions.processComplexAssertions !== undefined ?
        userOptions.processComplexAssertions : this.PROCESS_COMPLEX_ASSERTIONS,
        
      optimizeSSAGeneration:
        userOptions.optimizeSSAGeneration !== undefined ?
        userOptions.optimizeSSAGeneration : this.OPTIMIZE_SSA_GENERATION,
        
      // Runtime checks
      insertRuntimeChecks:
        userOptions.insertRuntimeChecks !== undefined ?
        userOptions.insertRuntimeChecks : this.INSERT_RUNTIME_CHECKS,
        
      generateAssertions:
        userOptions.generateAssertions !== undefined ?
        userOptions.generateAssertions : this.GENERATE_ASSERTIONS,
        
      treatWarningsAsErrors:
        userOptions.treatWarningsAsErrors !== undefined ?
        userOptions.treatWarningsAsErrors : this.TREAT_WARNINGS_AS_ERRORS,
        
      validateResults:
        userOptions.validateResults !== undefined ?
        userOptions.validateResults : this.VALIDATE_RESULTS
    };
  }
};

// Default export for convenience
export default {
  transformToSSA: enhancedTransformToSSA,
  options: SSATransformationOptions,
  createConfig: createEdgeCaseConfig,
  validate: validateSSAProgram
};
