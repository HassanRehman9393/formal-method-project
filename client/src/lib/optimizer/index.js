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

export {
  optimizeSSA,
  propagateConstants,
  eliminateDeadCode,
  eliminateCommonSubexpressions,
  analyzeDataFlow,
  buildSSAGraph
};
