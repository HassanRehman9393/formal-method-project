/**
 * SSA Optimization Module
 * 
 * Provides optimizations for SSA form code including:
 * - Constant propagation
 * - Dead code elimination
 * - Common subexpression elimination
 */

import { optimizeSSA } from './optimizationPipeline.js';
import { propagateConstants } from './constantPropagation.js';
import { eliminateDeadCode } from './deadCodeElimination.js';
import { eliminateCommonSubexpressions } from './commonSubexpressionElimination.js';
import { analyzeDataFlow } from './dataFlowAnalysis.js';
import { buildSSAGraph } from './ssaGraph.js';
import { addVisualizationMetadata, generateOptimizationSummary, OptimizationColors } from './visualizer.js';

/**
 * Apply optimizations with visualization metadata
 * @param {object} ssaProgram - Original SSA program
 * @param {object} options - Optimization options
 * @returns {object} Visualization-enhanced optimized program
 */
function optimizeWithVisualization(ssaProgram, options = {}) {
  // Keep the original for comparison
  const originalProgram = JSON.parse(JSON.stringify(ssaProgram));
  
  // Run optimization pipeline
  const { program: optimizedProgram, metadata } = optimizeSSA(ssaProgram, options);
  
  // Store before/after instruction counts
  metadata.before = originalProgram;
  metadata.after = optimizedProgram;
  
  // Add visualization metadata
  const visualProgram = addVisualizationMetadata(originalProgram, optimizedProgram, metadata);
  
  // Generate summary
  const summary = generateOptimizationSummary(metadata);
  
  return {
    program: visualProgram,
    metadata,
    summary,
    original: originalProgram
  };
}

export {
  optimizeSSA,
  optimizeWithVisualization,
  propagateConstants,
  eliminateDeadCode,
  eliminateCommonSubexpressions,
  analyzeDataFlow,
  buildSSAGraph,
  addVisualizationMetadata,
  generateOptimizationSummary,
  OptimizationColors
};
