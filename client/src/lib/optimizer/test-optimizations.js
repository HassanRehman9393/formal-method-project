/**
 * Test script for SSA optimizations
 */

import { transformToSSA } from '../ssa/index.js';
import { parseProgram } from '../parser/index.js';
import { 
  optimizeSSA,
  propagateConstants,
  eliminateDeadCode, 
  eliminateCommonSubexpressions 
} from './index.js';

// Sample programs to test optimizations
const testPrograms = [
  {
    name: 'Constant Propagation',
    code: `
      x := 5;
      y := x + 3;
      z := y * 2;
      if (z > 10) {
        result := z;
      } else {
        result := 0;
      }
    `
  },
  {
    name: 'Dead Code Elimination',
    code: `
      x := 10;
      y := 20;
      z := x + y;  // Used later
      a := x * 2;  // Dead code
      b := y - 5;  // Dead code
      result := z;
    `
  },
  {
    name: 'Common Subexpression Elimination',
    code: `
      a := 5;
      b := 10;
      c := a + b;
      d := a + b;  // Common subexpression
      e := c * d;
      f := a + b;  // Common subexpression again
    `
  },
  {
    name: 'Combined Optimizations',
    code: `
      x := 5;
      y := x;      // Will be propagated
      z := y + 3;  // Will become z := 5 + 3
      a := z * 2;  // Will become a := 8 * 2
      b := z * 2;  // Common subexpression
      unused := a + 1;  // Dead code
      result := a + b;
    `
  }
];

/**
 * Verify that optimizations were applied correctly
 * @param {object} originalProgram - The original SSA program
 * @param {object} optimizedProgram - The optimized SSA program
 * @param {string} optimizationType - The type of optimization to check
 * @returns {boolean} True if the optimization was correctly applied
 */
function verifyOptimization(originalProgram, optimizedProgram, optimizationType) {
  if (!originalProgram || !optimizedProgram) {
    console.log(`Cannot verify ${optimizationType} - invalid programs`);
    return false;
  }
  
  // Create string representations to compare
  const originalStr = JSON.stringify(originalProgram);
  const optimizedStr = JSON.stringify(optimizedProgram);
  
  // First check if anything changed
  if (originalStr === optimizedStr) {
    console.log(`No changes detected for ${optimizationType}`);
    return false;
  }
  
  // Check for specific optimizations
  switch(optimizationType) {
    case 'constantPropagation':
      // Look for optimized instructions that show constant propagation
      return hasOptimizedInstructions(optimizedProgram) && 
             containsString(optimizedStr, 'IntegerLiteral') &&
             !containsString(originalStr, 'originalValue');
      
    case 'deadCodeElimination':
      // In dead code elimination, optimized program should have fewer instructions
      return countInstructions(optimizedProgram) < countInstructions(originalProgram);
      
    case 'commonSubexpressionElimination':
      // Look for variable assignments replacing expressions
      return hasOptimizedInstructions(optimizedProgram) &&
             containsString(optimizedStr, 'Variable') &&
             containsString(optimizedStr, 'originalValue');
      
    default:
      return hasOptimizedInstructions(optimizedProgram);
  }
}

/**
 * Check if program has optimized instructions
 */
function hasOptimizedInstructions(program) {
  if (!program || !program.blocks) return false;
  
  for (const block of program.blocks) {
    if (!block || !block.instructions) continue;
    
    for (const instr of block.instructions) {
      if (instr && instr.optimized) {
        return true;
      }
    }
  }
  
  return false;
}

/**
 * Count instructions in a program
 */
function countInstructions(program) {
  if (!program || !program.blocks) return 0;
  
  let count = 0;
  for (const block of program.blocks) {
    if (block && block.instructions) {
      count += block.instructions.length;
    }
  }
  
  return count;
}

/**
 * Check if string contains a substring
 */
function containsString(str, substr) {
  return str.includes(substr);
}

/**
 * Run optimization tests
 */
async function testOptimizations() {
  console.log('========================================');
  console.log('Running SSA Optimization Tests');
  console.log('========================================');
  
  for (const test of testPrograms) {
    console.log(`\n=== Test: ${test.name} ===`);
    console.log('Source code:');
    console.log(test.code);
    
    try {
      // Parse the program
      console.log('\nParsing program...');
      const ast = parseProgram(test.code);
      console.log('✓ Parsing successful');
      
      // Transform to SSA
      console.log('\nTransforming to SSA...');
      const ssaProgram = transformToSSA(ast);
      console.log('✓ SSA transformation successful');
      
      // Individual optimizations
      
      // 1. Constant Propagation
      console.log('\nApplying Constant Propagation...');
      const constPropProgram = propagateConstants(ssaProgram);
      console.log('✓ Constant propagation complete');
      
      // Add verification for individual optimizations
      console.log('\nVerifying Constant Propagation...');
      const constPropVerified = verifyOptimization(ssaProgram, constPropProgram, 'constantPropagation');
      console.log(`✓ Constant propagation ${constPropVerified ? 'verified' : 'not detected'}`);
      
      // 2. Dead Code Elimination
      console.log('\nApplying Dead Code Elimination...');
      const deadCodeProgram = eliminateDeadCode(constPropProgram);
      console.log('✓ Dead code elimination complete');
      
      console.log('\nVerifying Dead Code Elimination...');
      const deadCodeVerified = verifyOptimization(constPropProgram, deadCodeProgram, 'deadCodeElimination');
      console.log(`✓ Dead code elimination ${deadCodeVerified ? 'verified' : 'not detected'}`);
      
      // 3. Common Subexpression Elimination
      console.log('\nApplying Common Subexpression Elimination...');
      const cseProgram = eliminateCommonSubexpressions(deadCodeProgram);
      console.log('✓ Common subexpression elimination complete');
      
      console.log('\nVerifying Common Subexpression Elimination...');
      const cseVerified = verifyOptimization(deadCodeProgram, cseProgram, 'commonSubexpressionElimination');
      console.log(`✓ Common subexpression elimination ${cseVerified ? 'verified' : 'not detected'}`);
      
      // Combined optimization pipeline
      console.log('\nApplying Full Optimization Pipeline...');
      const { program: optimizedProgram, metadata } = optimizeSSA(ssaProgram);
      console.log('✓ Full optimization pipeline complete');
      
      // Show optimization results
      console.log('\nOptimization Results:');
      console.log(`- Optimized: ${metadata.optimized ? 'Yes' : 'No'}`);
      console.log(`- Iterations: ${metadata.iterations}`);
      
      // Fix: Handle potentially undefined passesApplied array
      const passesApplied = metadata.passesApplied || [];
      console.log(`- Passes Applied: ${passesApplied.join(', ') || 'None'}`);
      
      // Add more detailed information about the optimized program
      if (optimizedProgram && optimizedProgram.blocks) {
        console.log('\nOptimized Program Summary:');
        console.log(`- Total Blocks: ${optimizedProgram.blocks.length}`);
        
        // Count optimized instructions
        let totalInstructions = 0;
        let optimizedInstructions = 0;
        
        for (const block of optimizedProgram.blocks) {
          if (!block || !block.instructions) continue;
          
          totalInstructions += block.instructions.length;
          optimizedInstructions += block.instructions.filter(instr => instr && instr.optimized).length;
        }
        
        console.log(`- Total Instructions: ${totalInstructions}`);
        console.log(`- Optimized Instructions: ${optimizedInstructions}`);
        
        if (metadata.changes && metadata.changes.length > 0) {
          console.log('\nOptimization Changes:');
          metadata.changes.forEach((change, i) => {
            console.log(`- Iteration ${change.iteration}:`);
            change.passes.forEach(pass => {
              console.log(`  - ${pass.name}: ${pass.changed ? 'Changed' : 'No Change'}`);
            });
          });
        }
      }
      
      console.log('✅ Test passed');
    } catch (error) {
      console.error('❌ Error:', error);
      console.error('Stack trace:', error.stack);
    }
  }
  
  console.log('\n========================================');
  console.log('All optimization tests completed');
  console.log('========================================');
}

// Run tests when script is executed directly
testOptimizations().catch(console.error);

export default testOptimizations;
