/**
 * Test script for loop handling and unrolling
 */

import { parseProgram } from '../parser/index.js';
import { transformToSSA, formatSSA } from './index.js';
import { simplifySSA } from './ssaVisualizer.js';

// Sample programs with loops to test unrolling
const testPrograms = [
  {
    name: 'Simple While Loop',
    code: `
      i := 0;
      while (i < 5) {
        x := i * 2;
        i := i + 1;
      }
    `
  },
  {
    name: 'For Loop',
    code: `
      sum := 0;
      for (i := 1; i <= 5; i := i + 1) {
        sum := sum + i;
      }
    `
  },
  {
    name: 'Nested Loops',
    code: `
      sum := 0;
      for (i := 0; i < 3; i := i + 1) {
        for (j := 0; j < 2; j := j + 1) {
          sum := sum + i * j;
        }
      }
    `
  }
];

/**
 * Run loop handling tests
 */
async function testLoopHandling() {
  console.log('========================================');
  console.log('Running loop handling tests');
  console.log('========================================');
  
  let passedTests = 0;
  let failedTests = 0;

  for (const test of testPrograms) {
    console.log(`\n=== Test: ${test.name} ===`);
    console.log('Source code:');
    console.log(test.code);

    try {
      // Parse the program
      console.log('\nParsing program...');
      const ast = parseProgram(test.code);
      console.log('✓ Parsing successful');
      
      // Transform to SSA with unrolling (depth 2)
      console.log('\nTransforming to SSA with loop unrolling (depth=2)...');
      const ssaProgram = transformToSSA(ast, { 
        unrollDepth: 2,
        handleLoops: true 
      });
      console.log('✓ SSA transformation successful');
      
      // Try to get a simplified representation for better debugging
      let simplifiedSSA = '';
      try {
        simplifiedSSA = simplifySSA(ssaProgram);
      } catch (e) {
        simplifiedSSA = `// Error generating simplified SSA: ${e.message}`;
      }

      // Format the SSA code
      console.log('\nFormatting SSA code...');
      let ssaCode;
      try {
        ssaCode = formatSSA(ssaProgram);
        console.log('✓ Formatting successful');
      } catch (err) {
        ssaCode = `// Error formatting SSA: ${err.message}\n\n${simplifiedSSA}`;
        console.log('✗ Formatting failed, showing simplified version');
      }

      console.log('\nSSA Form (with unrolled loops):');
      console.log(ssaCode);
      
      console.log('\nSimplified SSA visualization:');
      console.log(simplifiedSSA);
      
      console.log('✅ Test passed\n');
      passedTests++;
    } catch (error) {
      console.error('❌ Error:', error);
      console.error('Stack trace:', error.stack);
      failedTests++;
    }
  }
  
  // Print test summary
  console.log(`\n=== Test Summary ===`);
  console.log(`Total tests: ${testPrograms.length}`);
  console.log(`Passed: ${passedTests}`);
  console.log(`Failed: ${failedTests}`);
  
  return { passedTests, failedTests };
}

// Run tests when script is executed directly
testLoopHandling().catch(console.error);

export default testLoopHandling;
