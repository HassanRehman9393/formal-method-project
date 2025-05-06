/**
 * Debug script for optimizer
 */

import { parse } from '../parser/parser.js';
import { transformToSSA } from '../ssa/ssaTransformer.js';
import { optimizeSSA } from './optimizationPipeline.js';
import { constantPropagation } from './constantPropagation.js';

// Simple test program
const testProgram = `
  x := 5;
  y := 10;
  z := x + y;  // Should be optimized to z := 15
`;

// Simple constant propagation implementation for debugging
function simpleConstantProp(ssaProgram) {
  // Create a deep clone to avoid modifying the original
  const result = JSON.parse(JSON.stringify(ssaProgram));

  // Step 1: Build a map of all constants
  const constants = new Map();
  
  console.log("Building constants map:");
  // Pre-scan all blocks for constants
  for (const block of result.blocks || []) {
    if (!block || !block.instructions) continue;
    
    for (const instr of block.instructions) {
      if (instr?.type === 'Assignment') {
        // Direct constant assignments
        if (instr.value?.type === 'IntLiteral' || instr.value?.type === 'IntegerLiteral') {
          constants.set(instr.target, instr.value.value);
          console.log(`  ${instr.target} = ${instr.value.value}`);
        }
      }
    }
  }
  
  // Step 2: Propagate constants
  let optimizationsMade = false;
  console.log("\nLooking for expressions to optimize:");
  
  for (const block of result.blocks || []) {
    if (!block || !block.instructions) continue;
    
    for (let i = 0; i < block.instructions.length; i++) {
      const instr = block.instructions[i];
      if (!instr || instr.type !== 'Assignment') continue;
      
      // Skip if this is directly a constant
      if (instr.value?.type === 'IntLiteral' || instr.value?.type === 'IntegerLiteral') continue;
      
      // Look for binary expressions where both operands are constants
      if (instr.value?.type === 'BinaryExpression') {
        const expr = instr.value;
        
        let leftValue = null;
        let rightValue = null;
        
        // Get left operand value
        if (expr.left?.type === 'Identifier' || expr.left?.type === 'Variable') {
          const varName = expr.left.name;
          
          // Try with SSA version if available
          let lookupName = varName;
          if (expr.left.ssaVersion !== undefined) {
            lookupName = `${varName}_${expr.left.ssaVersion}`;
          }
          
          if (constants.has(lookupName)) {
            leftValue = constants.get(lookupName);
          } else if (constants.has(varName)) {
            leftValue = constants.get(varName);
          }
          
          console.log(`  Left operand ${lookupName}: ${leftValue !== null ? leftValue : 'not constant'}`);
          
        } else if (expr.left?.type === 'IntLiteral' || expr.left?.type === 'IntegerLiteral') {
          leftValue = expr.left.value;
        }
        
        // Get right operand value
        if (expr.right?.type === 'Identifier' || expr.right?.type === 'Variable') {
          const varName = expr.right.name;
          
          // Try with SSA version if available
          let lookupName = varName;
          if (expr.right.ssaVersion !== undefined) {
            lookupName = `${varName}_${expr.right.ssaVersion}`;
          }
          
          if (constants.has(lookupName)) {
            rightValue = constants.get(lookupName);
          } else if (constants.has(varName)) {
            rightValue = constants.get(varName);
          }
          
          console.log(`  Right operand ${lookupName}: ${rightValue !== null ? rightValue : 'not constant'}`);
          
        } else if (expr.right?.type === 'IntLiteral' || expr.right?.type === 'IntegerLiteral') {
          rightValue = expr.right.value;
        }
        
        // If both operands are constants, fold the expression
        if (leftValue !== null && rightValue !== null) {
          let resultValue;
          switch (expr.operator) {
            case '+': resultValue = leftValue + rightValue; break;
            case '-': resultValue = leftValue - rightValue; break;
            case '*': resultValue = leftValue * rightValue; break;
            case '/': resultValue = rightValue !== 0 ? Math.floor(leftValue / rightValue) : null; break;
            default: resultValue = null;
          }
          
          if (resultValue !== null) {
            console.log(`  Optimizing ${instr.target}: ${leftValue} ${expr.operator} ${rightValue} = ${resultValue}`);
            
            // Replace with optimized constant
            block.instructions[i] = {
              ...instr,
              value: { type: 'IntLiteral', value: resultValue },
              optimized: true,
              optimizationType: 'ConstantPropagation',
              originalValue: JSON.parse(JSON.stringify(instr.value))
            };
            
            optimizationsMade = true;
            
            // Add to constants map for further propagation
            constants.set(instr.target, resultValue);
          }
        }
      }
    }
  }
  
  // Add metadata
  result.metadata = {
    ...result.metadata,
    constantPropagationApplied: optimizationsMade
  };
  
  return result;
}

// Direct invocation of the pipeline stages
async function debugDirectPipeline() {
  console.log("=== DIRECT PIPELINE DEBUG ===");
  
  // Step 1: Parse
  console.log("Parsing program...");
  const ast = parse(testProgram);
  
  // Step 2: Manual transformation to SSA
  console.log("\nCreating SSA AST...");
  const ssaAST = {
    type: 'Program',
    body: [
      { 
        type: 'AssignmentStatement',
        left: { type: 'Identifier', name: 'x', ssaVersion: 1 },
        right: { type: 'IntLiteral', value: 5 }
      },
      {
        type: 'AssignmentStatement',
        left: { type: 'Identifier', name: 'y', ssaVersion: 1 },
        right: { type: 'IntLiteral', value: 10 }
      },
      {
        type: 'AssignmentStatement',
        left: { type: 'Identifier', name: 'z', ssaVersion: 1 },
        right: {
          type: 'BinaryExpression',
          operator: '+',
          left: { type: 'Identifier', name: 'x', ssaVersion: 1 },
          right: { type: 'Identifier', name: 'y', ssaVersion: 1 }
        }
      }
    ]
  };
  
  // Create a minimal SSA program structure with blocks format
  const manualSSAProgram = {
    ssaAST,
    blocks: [
      {
        label: 'entry',
        instructions: [
          { 
            type: 'Assignment',
            target: 'x_1',
            value: { type: 'IntLiteral', value: 5 }
          },
          {
            type: 'Assignment',
            target: 'y_1',
            value: { type: 'IntLiteral', value: 10 }
          },
          {
            type: 'Assignment',
            target: 'z_1',
            value: {
              type: 'BinaryExpression',
              operator: '+',
              left: { type: 'Identifier', name: 'x', ssaVersion: 1 },
              right: { type: 'Identifier', name: 'y', ssaVersion: 1 }
            }
          }
        ],
        terminator: { type: 'Jump', target: 'exit' }
      },
      {
        label: 'exit',
        instructions: [],
        terminator: null
      }
    ],
    variableVersions: {
      x: 1,
      y: 1,
      z: 1
    },
    metadata: {
      transformationTime: 0,
      loopUnrollDepth: 3,
      variablesTransformed: 3,
      phiNodeCount: 0
    }
  };
  
  console.log("\n=== RUNNING SIMPLE CONSTANT PROPAGATION ===");
  const simpleResult = simpleConstantProp(manualSSAProgram);
  
  // Check for optimizations
  console.log("\nChecking for optimized instructions:");
  let foundSimpleOptimized = false;
  if (simpleResult.blocks) {
    simpleResult.blocks.forEach((block, blockIdx) => {
      if (block && block.instructions) {
        block.instructions.forEach((instr, instrIdx) => {
          if (instr && instr.optimized) {
            console.log(`Block ${blockIdx}, instruction ${instrIdx} optimized:`);
            console.log(`  Target: ${instr.target}`);
            console.log(`  Original: ${JSON.stringify(instr.originalValue)}`);
            console.log(`  New value: ${JSON.stringify(instr.value)}`);
            foundSimpleOptimized = true;
          }
        });
      }
    });
  }
  
  if (!foundSimpleOptimized) {
    console.log("No optimized instructions found in simple implementation");
  }
  
  console.log("\nRunning original constant propagation for comparison...");
  
  // Step 3: Run constant propagation directly
  try {
    const result = constantPropagation(manualSSAProgram);
    console.log("Constant propagation result:", {
      applied: result.metadata?.constantPropagationApplied,
      count: result.metadata?.constantsPropagated
    });
    
    // Check if any instructions were optimized
    if (result.blocks && result.blocks.length > 0) {
      console.log("\nChecking for optimized instructions:");
      let foundOptimized = false;
      
      result.blocks.forEach((block, blockIdx) => {
        if (block && block.instructions) {
          block.instructions.forEach((instr, instrIdx) => {
            if (instr && instr.optimized) {
              console.log(`- Block ${blockIdx}, instruction ${instrIdx} optimized`);
              console.log('  Target:', instr.target);
              console.log('  Original:', JSON.stringify(instr.originalValue));
              console.log('  New value:', JSON.stringify(instr.value));
              foundOptimized = true;
            }
          });
        }
      });
      
      if (!foundOptimized) {
        console.log("No optimized instructions found");
      }
    }
    
    // Run full optimization pipeline
    console.log("\nRunning full optimization pipeline...");
    const fullOptResult = optimizeSSA(manualSSAProgram);
    
    console.log("Full optimization result:", {
      passes: fullOptResult.metadata?.passesApplied || [],
      optimized: fullOptResult.metadata?.optimized
    });
    
  } catch (error) {
    console.error("Error during optimization:", error);
  }
}

// Run the debug pipeline
debugDirectPipeline(); 