/**
 * SSA Transformer Module
 * 
 * Optimized version with better performance and handling of complex cases
 */

// Import necessary modules and helper functions
import { transformLoops } from './loopHandler.js';
import { buildCFG } from './cfgBuilder.js';
import { handleArrayBounds } from './arrayBoundsAnalysis.js';
import { processComplexControlFlow } from './complexControlFlow.js';
import { processComplexAssertions } from './complexAssertions.js';
import { handleEdgeCases } from './edgeCases.js';
import { SSANode, PhiNode, VariableNode } from './ssaNodes.js';

// Optimization: Use Map instead of Object for better performance with lookups
export function transformToSSA(ast, options = {}) {
  // Initialize configuration
  const config = {
    loopUnrollDepth: options.loopUnrollDepth || 3,
    optimizePhiNodes: options.optimizePhiNodes !== false,
    handleArrays: options.handleArrays !== false,
    trackVariableVersions: options.trackVariableVersions !== false
  };
  
  // Start time for performance tracking
  const startTime = Date.now();
  
  try {
    // Pre-process AST, handle edge cases
    const processedAST = handleEdgeCases(ast);
    
    // Transform loops into if-else chains based on unrolling depth
    const unrolledAST = transformLoops(processedAST, config.loopUnrollDepth);
    
    // Build the control flow graph
    const cfg = buildCFG(unrolledAST);
    
    // Perform the main SSA transformation
    const result = performSSATransformation(unrolledAST, cfg, config);
    
    // Add performance metrics
    result.metadata = {
      transformationTime: Date.now() - startTime,
      loopUnrollDepth: config.loopUnrollDepth,
      variablesTransformed: result.variableVersions ? Object.keys(result.variableVersions).length : 0,
      phiNodeCount: countPhiNodes(result.ssaAST)
    };
    
    return result;
  } catch (error) {
    // Add source location to error if available
    if (error.node && error.node.location) {
      error.message = `${error.message} at line ${error.node.location.start.line}, column ${error.node.location.start.column}`;
    }
    throw error;
  }
}

/**
 * Main SSA transformation function - optimized for performance
 */
function performSSATransformation(ast, cfg, config) {
  // Ensure CFG has expected properties
  if (!cfg || !cfg.nodes) {
    console.warn('Invalid CFG provided to SSA transformer, creating minimal CFG');
    cfg = { 
      nodes: [],
      blocks: [], // For compatibility
      getBlock: () => null
    };
  }
  
  // Normalize CFG structure for compatibility
  // Some code might expect cfg.blocks, others cfg.nodes
  if (!cfg.blocks && cfg.nodes) {
    cfg.blocks = cfg.nodes;
  } else if (!cfg.nodes && cfg.blocks) {
    cfg.nodes = cfg.blocks;
  }
  
  // Ensure getBlock method exists
  if (!cfg.getBlock) {
    cfg.getBlock = (id) => cfg.blocks.find(block => block.id === id || block.label === id) || null;
  }
  
  // Initialize SSA context
  const context = {
    variableVersions: new Map(), // Maps variable names to their current version number
    variableValues: new Map(),   // Maps variable.version to their defining nodes
    currentBlock: null,          // Current basic block being processed
    allBlocks: cfg.blocks || [],  // All basic blocks in the CFG
    phiNodes: new Map(),         // Maps block IDs to their phi nodes
    loopDepth: config.loopUnrollDepth,
    arrays: new Map(),           // Tracks array variables
    usedVariables: new Set(),    // Tracks which variables are actually used
    results: {                   // Store results
      ssaAST: null,
      variableVersions: {},
      cfg: cfg,
      blocks: [] // Initialize blocks array
    }
  };
  
  // Add phi nodes at control flow merge points
  insertPhiNodes(cfg, context);
  
  // Transform each node to SSA form (deep copy to avoid modifying original)
  context.results.ssaAST = transformNode(JSON.parse(JSON.stringify(ast)), context);
  
  // Convert Maps back to plain objects for result
  context.results.variableVersions = Object.fromEntries(context.variableVersions);
  
  // Convert CFG nodes to blocks
  context.results.blocks = cfg.blocks.map(block => ({
    label: block.label || block.id,
    instructions: block.statements || [],
    terminator: block.terminator || null,
    predecessors: block.predecessors || [],
    successors: block.successors || []
  }));
  
  // Optimize phi nodes if configured to do so
  if (config.optimizePhiNodes) {
    optimizePhiNodes(context.results.ssaAST, context);
  }
  
  // Handle array bounds analysis if configured
  if (config.handleArrays) {
    handleArrayBounds(context.results.ssaAST, context.arrays);
  }
  
  // Process any complex control flow patterns
  processComplexControlFlow(context.results.ssaAST);
  
  // Process complex assertions
  processComplexAssertions(context.results.ssaAST);
  
  return context.results;
}

/**
 * Inserts phi nodes at control flow merge points
 * Optimized with an efficient dominance frontier calculation
 */
function insertPhiNodes(cfg, context) {
  // Handle incomplete CFG gracefully
  if (!cfg || !cfg.blocks || !Array.isArray(cfg.blocks) || cfg.blocks.length === 0) {
    console.warn('Incomplete CFG provided to insertPhiNodes');
    return;
  }
  
  try {
    // Calculate dominance frontiers for each block
    const dominanceFrontiers = calculateDominanceFrontiers(cfg);
    
    // Track variables that need phi nodes
    const variablesNeedingPhis = new Map();
    
    // Find variables that are assigned in the program
    for (const block of cfg.blocks) {
      // Ensure the block and its statements are valid
      if (!block || !block.statements || !Array.isArray(block.statements)) {
        continue;
      }
      
      // Variables assigned in this block
      const assignedVars = new Set();
      
      // Check all statements in the block for assignments
      for (const statement of block.statements) {
        const assignedVar = getAssignedVariable(statement);
        if (assignedVar) {
          assignedVars.add(assignedVar);
          
          // Initialize entry in the map if not exists
          if (!variablesNeedingPhis.has(assignedVar)) {
            variablesNeedingPhis.set(assignedVar, new Set());
          }
        }
      }
      
      // For each assigned variable, add phi nodes in the dominance frontier
      for (const variable of assignedVars) {
        const frontier = dominanceFrontiers.get(block.id || block.label) || [];
        for (const frontierBlock of frontier) {
          variablesNeedingPhis.get(variable).add(frontierBlock);
        }
      }
    }
    
    // Insert phi nodes for each variable at each required location
    for (const [variable, blocks] of variablesNeedingPhis.entries()) {
      for (const blockId of blocks) {
        const block = cfg.getBlock ? cfg.getBlock(blockId) : 
                     cfg.blocks.find(b => b.id === blockId || b.label === blockId);
        if (!block) continue;
        
        // Initialize phi nodes map for this block if needed
        if (!context.phiNodes.has(blockId)) {
          context.phiNodes.set(blockId, new Map());
        }
        
        // Add phi node for this variable if not already present
        if (!context.phiNodes.get(blockId).has(variable)) {
          context.phiNodes.get(blockId).set(variable, {
            type: 'PhiNode',
            variable: variable,
            operands: [], // Will be filled during transformation
            location: (block.statements && block.statements.length > 0) ? 
                      block.statements[0]?.location : null
          });
        }
      }
    }
  } catch (error) {
    console.error('Error inserting phi nodes:', error);
    // Gracefully handle errors by not inserting phi nodes
  }
}

/**
 * Efficiently calculates dominance frontiers for the CFG
 * Uses an iterative approach for better performance than recursive
 */
function calculateDominanceFrontiers(cfg) {
  // Handle incomplete CFG gracefully
  if (!cfg || !cfg.blocks || !Array.isArray(cfg.blocks) || cfg.blocks.length === 0) {
    console.warn('Incomplete CFG provided to calculateDominanceFrontiers');
    return new Map();
  }
  
  try {
    // First calculate the dominators for each block
    const dominators = calculateDominators(cfg);
    
    // Initialize dominance frontiers
    const dominanceFrontiers = new Map();
    for (const block of cfg.blocks) {
      if (block && (block.id || block.label)) {
        dominanceFrontiers.set(block.id || block.label, []);
      }
    }
    
    // Calculate dominance frontiers for each block
    for (const block of cfg.blocks) {
      // Skip if block is invalid or has fewer than 2 predecessors
      if (!block || !block.predecessors || block.predecessors.length < 2) continue;
      
      const blockId = block.id || block.label;
      if (!blockId) continue;
      
      for (const pred of block.predecessors) {
        let runner = pred;
        const idom = dominators.get(blockId);
        
        // Find all nodes that are in the path from pred to idom
        while (runner !== idom && runner !== undefined) {
          if (dominanceFrontiers.has(runner)) {
            dominanceFrontiers.get(runner).push(blockId);
          }
          runner = dominators.get(runner);
        }
      }
    }
    
    return dominanceFrontiers;
  } catch (error) {
    console.error('Error calculating dominance frontiers:', error);
    return new Map(); // Return empty map to allow graceful degradation
  }
}

/**
 * Calculate dominators for each block in the CFG
 * Uses the iterative algorithm for better performance
 */
function calculateDominators(cfg) {
  // Handle incomplete CFG gracefully
  if (!cfg || !cfg.blocks || !Array.isArray(cfg.blocks) || cfg.blocks.length === 0) {
    console.warn('Incomplete CFG provided to calculateDominators');
    return new Map();
  }
  
  try {
    const blocks = cfg.blocks;
    const dominators = new Map();
    
    // Get the entry block - if none exists, use the first one
    const entryBlockId = cfg.entry?.id || cfg.entryNode?.id || 
                         cfg.entry?.label || cfg.entryNode?.label || 
                         (blocks[0] && (blocks[0].id || blocks[0].label));
    
    if (!entryBlockId) {
      console.warn('No entry block found in CFG');
      return dominators;
    }
    
    // Initialize all blocks to be dominated by all blocks
    const allBlockIds = blocks.map(b => b && (b.id || b.label)).filter(Boolean);
    if (allBlockIds.length === 0) return dominators;
    
    // Initialize dominators
    for (const block of blocks) {
      if (!block) continue;
      const blockId = block.id || block.label;
      if (!blockId) continue;
      
      dominators.set(blockId, blockId === entryBlockId ? 
        new Set([entryBlockId]) : 
        new Set(allBlockIds));
    }
    
    // Iteratively refine the dominators
    let changed = true;
    const MAX_ITERATIONS = 1000; // Safety limit
    let iteration = 0;
    
    while (changed && iteration < MAX_ITERATIONS) {
      changed = false;
      iteration++;
      
      for (const block of blocks) {
        // Skip invalid blocks or the entry block
        if (!block || !block.predecessors) continue;
        const blockId = block.id || block.label;
        if (!blockId || blockId === entryBlockId) continue;
        
        // Calculate new dominators based on predecessors
        let newDoms = new Set(allBlockIds);
        let first = true;
        
        for (const pred of block.predecessors) {
          const predDoms = dominators.get(pred);
          if (!predDoms) continue;
          
          if (first) {
            // For the first predecessor, start with its dominators
            newDoms = new Set(predDoms);
            first = false;
          } else {
            // Intersect with current dominator set
            newDoms = new Set([...newDoms].filter(id => predDoms.has(id)));
          }
        }
        
        // Add the block itself
        newDoms.add(blockId);
        
        // Check if dominators changed
        const oldDoms = dominators.get(blockId);
        if (!oldDoms || 
            oldDoms.size !== newDoms.size || 
            ![...oldDoms].every(id => newDoms.has(id))) {
          dominators.set(blockId, newDoms);
          changed = true;
        }
      }
    }
    
    if (iteration >= MAX_ITERATIONS) {
      console.warn('Dominator calculation reached iteration limit, result may be inaccurate');
    }
    
    // Convert from sets to immediate dominators
    const immediateDominators = new Map();
    for (const block of blocks) {
      if (!block) continue;
      const blockId = block.id || block.label;
      if (!blockId) continue;
      
      if (blockId === entryBlockId) {
        immediateDominators.set(blockId, null);
        continue;
      }
      
      const doms = dominators.get(blockId);
      if (!doms) continue;
      
      const candidates = new Set(doms);
      candidates.delete(blockId);
      
      // Find the immediate dominator (closest dominator)
      let idom = null;
      for (const dom of candidates) {
        let isImmediate = true;
        for (const other of candidates) {
          const otherDoms = dominators.get(other);
          if (other !== dom && otherDoms?.has(dom)) {
            isImmediate = false;
            break;
          }
        }
        if (isImmediate) {
          idom = dom;
          break;
        }
      }
      
      immediateDominators.set(blockId, idom);
    }
    
    return immediateDominators;
  } catch (error) {
    console.error('Error calculating dominators:', error);
    return new Map(); // Return empty map to allow graceful degradation
  }
}

/**
 * Transform an AST node to SSA form
 * Updated to cache results for better performance
 */
function transformNode(node, context, cache = new Map()) {
  // Return null for null/undefined nodes
  if (!node) return null;
  
  // Check if we've already transformed this exact node (for common subexpressions)
  const nodeKey = JSON.stringify(node);
  if (cache.has(nodeKey)) {
    return cache.get(nodeKey);
  }
  
  let result;
  
  switch (node.type) {
    case 'Program':
      result = transformProgram(node, context, cache);
      break;
    
    case 'BlockStatement':
      result = transformBlock(node, context, cache);
      break;
    
    case 'AssignmentStatement':
      result = transformAssignment(node, context, cache);
      break;
    
    case 'IfStatement':
      result = transformIfStatement(node, context, cache);
      break;
    
    case 'WhileStatement':
    case 'ForStatement':
      // Loops should be already unrolled by transformLoops
      // If they're not, handle as a special case
      result = transformUnrolledLoop(node, context, cache);
      break;
    
    case 'AssertStatement':
    case 'PostConditionStatement':
      result = transformAssertion(node, context, cache);
      break;
    
    case 'BinaryExpression':
      result = transformBinaryExpression(node, context, cache);
      break;
    
    case 'UnaryExpression':
      result = transformUnaryExpression(node, context, cache);
      break;
    
    case 'ArrayAccess':
      result = transformArrayAccess(node, context, cache);
      break;
    
    case 'Identifier':
      result = transformIdentifier(node, context);
      break;
    
    case 'IntLiteral':
    case 'BoolLiteral':
    case 'IntegerLiteral': // Handle different naming conventions
    case 'BooleanLiteral': // Handle different naming conventions
      result = node; // Literals stay the same
      break;
    
    case 'EmptyStatement':
      result = node; // Empty statements stay the same
      break;
    
    case 'ConditionalExpression':
      result = transformConditionalExpression(node, context, cache);
      break;
    
    default:
      // Handle unknown node types
      console.warn(`Unknown node type: ${node.type}`);
      result = node;
  }
  
  // Cache the result
  cache.set(nodeKey, result);
  
  return result;
}

/**
 * Get the variable being assigned in a statement
 */
function getAssignedVariable(statement) {
  if (!statement) return null;
  
  if (statement.type === 'AssignmentStatement') {
    const target = statement.left;
    if (target.type === 'Identifier') {
      return target.name;
    }
  }
  
  return null;
}

/**
 * Optimize phi nodes by removing unnecessary ones
 */
function optimizePhiNodes(ssaAST, context) {
  // Collect all phi nodes
  const phiNodes = [];
  collectPhiNodes(ssaAST, phiNodes);
  
  // Analyze dominance relationships to identify unnecessary phi nodes
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = phiNodes.length - 1; i >= 0; i--) {
      const phi = phiNodes[i];
      
      // If all operands are the same or are the phi itself, the phi is redundant
      const uniqueOperands = new Set();
      let selfReference = false;
      
      for (const operand of phi.operands) {
        if (operand === phi) {
          selfReference = true;
        } else {
          uniqueOperands.add(JSON.stringify(operand));
        }
      }
      
      // If there's only one unique operand (or it's all self-references)
      if (uniqueOperands.size === 1 || (uniqueOperands.size === 0 && selfReference)) {
        // Replace phi with its operand
        const replacement = selfReference ? null : 
          JSON.parse([...uniqueOperands][0]);
        
        // Replace all uses of this phi with the replacement
        replacePhiNode(ssaAST, phi, replacement);
        
        // Remove from the list
        phiNodes.splice(i, 1);
        changed = true;
      }
    }
  }
}

/**
 * Collect all phi nodes in the AST
 */
function collectPhiNodes(node, phiNodes) {
  if (!node || typeof node !== 'object') return;
  
  if (node.type === 'PhiNode') {
    phiNodes.push(node);
  }
  
  // Recursively process all properties
  for (const key in node) {
    if (node.hasOwnProperty(key) && typeof node[key] === 'object') {
      collectPhiNodes(node[key], phiNodes);
    }
  }
}

/**
 * Replace a phi node with its replacement
 */
function replacePhiNode(node, phiNode, replacement) {
  if (!node || typeof node !== 'object') return;
  
  // Replace in all properties
  for (const key in node) {
    if (!node.hasOwnProperty(key)) continue;
    
    if (node[key] === phiNode) {
      node[key] = replacement;
    } else if (typeof node[key] === 'object') {
      replacePhiNode(node[key], phiNode, replacement);
    }
  }
}

/**
 * Count phi nodes in the AST
 */
function countPhiNodes(node) {
  if (!node || typeof node !== 'object') return 0;
  
  let count = node.type === 'PhiNode' ? 1 : 0;
  
  // Recursively count in all properties
  for (const key in node) {
    if (node.hasOwnProperty(key) && typeof node[key] === 'object') {
      count += countPhiNodes(node[key]);
    }
  }
  
  return count;
}

// Implementation for transform functions...
function transformProgram(node, context, cache) {
  // Transform each statement in the program
  // Handle both node.body and node.statements for compatibility
  const statements = node.body || node.statements || [];
  const transformedStatements = statements.map(stmt => 
    transformNode(stmt, context, cache)
  ).filter(Boolean); // Filter out null statements
  
  return {
    ...node,
    type: 'Program',
    body: transformedStatements,
    statements: transformedStatements // Keep both for compatibility
  };
}

function transformBlock(node, context, cache) {
  // Transform each statement in the block
  // Handle both node.body and node.statements for compatibility
  const statements = node.body || node.statements || [];
  const transformedStatements = statements.map(stmt => 
    transformNode(stmt, context, cache)
  ).filter(Boolean); // Filter out null statements
  
  return {
    ...node,
    type: 'BlockStatement',
    body: transformedStatements,
    statements: transformedStatements // Keep both for compatibility
  };
}

function transformAssignment(node, context, cache) {
  // Transform the right side first
  const transformedRight = transformNode(node.right, context, cache);
  
  // Handle different target types
  if (node.left.type === 'Identifier') {
    const varName = node.left.name;
    
    // Get current version number or initialize to 0
    const currentVersion = context.variableVersions.get(varName) || 0;
    const newVersion = currentVersion + 1;
    
    // Update version number
    context.variableVersions.set(varName, newVersion);
    
    // Create new SSA node
    const ssaNode = {
      ...node,
      left: {
        ...node.left,
        ssaVersion: newVersion
      },
      right: transformedRight
    };
    
    // Store the assignment for future use
    if (!context.variableValues.has(varName)) {
      context.variableValues.set(varName, new Map());
    }
    context.variableValues.get(varName).set(newVersion, ssaNode);
    
    return ssaNode;
  } else if (node.left.type === 'ArrayAccess') {
    // Transform array access
    const transformedArray = transformNode(node.left.array, context, cache);
    const transformedIndex = transformNode(node.left.index, context, cache);
    
    // Track array variables
    const arrayName = getArrayName(node.left);
    if (arrayName && !context.arrays.has(arrayName)) {
      context.arrays.set(arrayName, {
        accesses: [],
        writes: []
      });
    }
    
    // Add this write to the tracking
    if (arrayName) {
      context.arrays.get(arrayName).writes.push({
        node: node,
        index: transformedIndex
      });
    }
    
    return {
      ...node,
      left: {
        ...node.left,
        array: transformedArray,
        index: transformedIndex
      },
      right: transformedRight
    };
  }
  
  // Fallback for unknown assignments
  return {
    ...node,
    right: transformedRight
  };
}

function transformIfStatement(node, context, cache) {
  // Transform the condition
  // Handle different property names (condition vs test)
  const condition = node.test || node.condition;
  const transformedCondition = transformNode(condition, context, cache);
  
  // Transform both branches
  // Handle different property names (consequent/thenBranch, alternate/elseBranch)
  const thenBranch = node.consequent || node.thenBranch;
  const elseBranch = node.alternate || node.elseBranch;
  
  const transformedThenBranch = transformNode(thenBranch, context, cache);
  const transformedElseBranch = elseBranch 
    ? transformNode(elseBranch, context, cache) 
    : null;
  
  return {
    ...node,
    type: 'IfStatement',
    test: transformedCondition,
    condition: transformedCondition, // Keep both for compatibility
    consequent: transformedThenBranch,
    thenBranch: transformedThenBranch, // Keep both for compatibility
    alternate: transformedElseBranch,
    elseBranch: transformedElseBranch // Keep both for compatibility
  };
}

function transformUnrolledLoop(node, context, cache) {
  // By this point, loops should be unrolled
  // However, we handle the case where they might not be
  console.warn(`Loop not unrolled before SSA transformation: ${node.type}`);
  
  // Transform condition and body
  // Handle different property names (condition vs test)
  const condition = node.test || node.condition;
  const transformedCondition = transformNode(condition, context, cache);
  const transformedBody = transformNode(node.body, context, cache);
  
  // Transform init and update for ForStatement
  let transformedInit = null;
  let transformedUpdate = null;
  
  if (node.type === 'ForStatement') {
    transformedInit = node.init ? transformNode(node.init, context, cache) : null;
    transformedUpdate = node.update ? transformNode(node.update, context, cache) : null;
  }
  
  // Result depends on node type
  if (node.type === 'WhileStatement') {
    return {
      ...node,
      type: 'WhileStatement',
      test: transformedCondition,
      condition: transformedCondition, // Keep both for compatibility
      body: transformedBody
    };
  } else { // ForStatement
    return {
      ...node,
      type: 'ForStatement',
      init: transformedInit,
      test: transformedCondition,
      condition: transformedCondition, // Keep both for compatibility
      update: transformedUpdate,
      body: transformedBody
    };
  }
}

function transformAssertion(node, context, cache) {
  // Transform the condition
  // Handle different property names (condition vs test)
  const condition = node.test || node.condition;
  const transformedCondition = transformNode(condition, context, cache);
  
  return {
    ...node,
    test: transformedCondition,
    condition: transformedCondition // Keep both for compatibility
  };
}

function transformBinaryExpression(node, context, cache) {
  // Transform both operands
  const transformedLeft = transformNode(node.left, context, cache);
  const transformedRight = transformNode(node.right, context, cache);
  
  // Before returning, make sure the types are correctly set for the optimizer
  // This ensures that binary expressions are properly recognized during optimization
  const result = {
    ...node,
    type: 'BinaryExpression',  // Ensure type is set
    operator: node.operator,   // Ensure operator is set
    left: transformedLeft,
    right: transformedRight
  };
  
  return result;
}

function transformUnaryExpression(node, context, cache) {
  // Transform the argument
  const transformedArgument = transformNode(node.argument, context, cache);
  
  return {
    ...node,
    argument: transformedArgument
  };
}

function transformArrayAccess(node, context, cache) {
  // Transform the array and index
  const transformedArray = transformNode(node.array, context, cache);
  const transformedIndex = transformNode(node.index, context, cache);
  
  // Track array accesses
  const arrayName = getArrayName(node);
  if (arrayName && !context.arrays.has(arrayName)) {
    context.arrays.set(arrayName, {
      accesses: [],
      writes: []
    });
  }
  
  // Add this access to the tracking
  if (arrayName) {
    context.arrays.get(arrayName).accesses.push({
      node: node,
      index: transformedIndex
    });
  }
  
  return {
    ...node,
    array: transformedArray,
    index: transformedIndex
  };
}

function transformIdentifier(node, context) {
  const varName = node.name;
  
  // Mark as used
  context.usedVariables.add(varName);
  
  // Get the current version
  const currentVersion = context.variableVersions.get(varName) || 0;
  
  // Return SSA version of the identifier
  return {
    ...node,
    ssaVersion: currentVersion,
    // Add these properties to make the SSA version visible to the optimizer
    type: 'Identifier',
    name: varName,
    version: currentVersion
  };
}

function transformConditionalExpression(node, context, cache) {
  // Transform test, consequent, and alternate
  const transformedTest = transformNode(node.test, context, cache);
  const transformedConsequent = transformNode(node.consequent, context, cache);
  const transformedAlternate = transformNode(node.alternate, context, cache);
  
  return {
    ...node,
    test: transformedTest,
    consequent: transformedConsequent,
    alternate: transformedAlternate
  };
}

/**
 * Get the base array name from an array access
 */
function getArrayName(node) {
  if (!node) return null;
  
  if (node.type === 'ArrayAccess') {
    return getArrayName(node.array);
  } else if (node.type === 'Identifier') {
    return node.name;
  }
  
  return null;
}

// Export additional helpers for testing
export {
  transformNode,
  insertPhiNodes,
  optimizePhiNodes
};
