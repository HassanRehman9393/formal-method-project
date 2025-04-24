/**
 * SSA Module
 * 
 * Exports functionality for transforming code to SSA form
 */

import SSATransformer from './ssaTransformer.js';
import { extractControlFlow } from './cfgBuilder.js';
import { Block, PhiFunction } from './ssaNodes.js';
import { detectLoops, unrollLoops } from './loopHandler.js';
import { simplifySSA } from './ssaVisualizer.js';

/**
 * Transform an AST to SSA form with optional loop unrolling
 * @param {object} ast - Abstract Syntax Tree
 * @param {object} options - Transformation options
 * @returns {object} Program in SSA form
 */
async function transformToSSA(ast, options = {}) {
  try {
    if (!ast) {
      console.error('No AST provided to SSA transformer');
      return createErrorSSA('No AST provided');
    }
    
    // Apply loop unrolling if requested
    let processedAst = ast;
    if (options.handleLoops !== false && options.unrollDepth > 0) {
      try {
        processedAst = unrollLoops(ast, {
          unrollDepth: options.unrollDepth,
          unrollAll: options.unrollAll || false
        });
      } catch (err) {
        console.error('Error during loop unrolling:', err);
        processedAst = ast; // Fall back to original AST
      }
    }
    
    const transformer = new SSATransformer(options);
    return transformer.transform(processedAst, options);
  } catch (error) {
    console.error('Error in SSA transformation:', error);
    return createErrorSSA(`Error: ${error.message}`);
  }
}

/**
 * Format SSA form as readable code
 * @param {object} ssaProgram - Program in SSA form
 * @returns {string} Formatted code representation
 */
function formatSSA(ssaProgram) {
  try {
    if (!ssaProgram) {
      return '// Error: No SSA program provided\n';
    }
    
    const transformer = new SSATransformer();
    return transformer.formatSSACode(ssaProgram);
  } catch (error) {
    console.error('Error formatting SSA:', error);
    return `// Error formatting SSA: ${error.message}\n`;
  }
}

/**
 * Create an error SSA program
 * @param {string} message - Error message
 * @returns {object} Error SSA program
 */
function createErrorSSA(message) {
  const errorBlock = new Block('error');
  errorBlock.addInstruction({
    type: 'Comment',
    text: message || 'Unknown error'
  });
  
  return {
    type: 'SSAProgram',
    blocks: [errorBlock]
  };
}

/**
 * Extract the control flow graph from an AST
 * @param {object} ast - Abstract Syntax Tree
 * @returns {object} Control flow graph
 */
function extractCFG(ast) {
  return extractControlFlow(ast);
}

/**
 * Analyze loops in an AST
 * @param {object} ast - Abstract Syntax Tree
 * @returns {object[]} Array of loop information objects
 */
function analyzeLoops(ast) {
  try {
    return detectLoops(ast);
  } catch (error) {
    console.error('Error analyzing loops:', error);
    return [];
  }
}

export {
  transformToSSA,
  formatSSA,
  extractCFG,
  SSATransformer,
  Block,
  PhiFunction,
  analyzeLoops,
  simplifySSA
};
