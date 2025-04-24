/**
 * Test script for SSA transformation
 * Tests basic SSA conversion features
 */

import { parseProgram } from '../parser/index.js';
import { transformToSSA, formatSSA } from './index.js';

// Sample programs to test SSA transformation
const testPrograms = [
  {
    name: 'Simple Assignment',
    code: 'x := 5;'
  },
  {
    name: 'Sequential Assignments',
    code: `
      x := 5;
      y := x + 3;
      z := x * y;
    `
  },
  {
    name: 'If Statement',
    code: `
      x := 10;
      if (x > 5) {
        y := x * 2;
      } else {
        y := x / 2;
      }
      z := y + 1;
    `
  },
  {
    name: 'While Loop',
    code: `
      sum := 0;
      i := 1;
      while (i <= 10) {
        sum := sum + i;
        i := i + 1;
      }
    `
  },
  {
    name: 'Assertion',
    code: `
      x := 5;
      y := x * 2;
      assert(y > x);
    `
  },
  {
    name: 'Nested If Statements',
    code: `
      x := 10;
      if (x > 5) {
        if (x > 8) {
          y := x * 3;
        } else {
          y := x * 2;
        }
      } else {
        y := x / 2;
      }
      z := y + 1;
    `
  },
  {
    name: 'Complex Expressions',
    code: `
      a := 5;
      b := 10;
      c := (a + b) * (a - b) / 2;
      d := c > 0 && a < b || !(c == 0);
    `
  },
  {
    name: 'For Loop',
    code: `
      sum := 0;
      for (i := 1; i <= 5; i := i + 1) {
        sum := sum + i * i;
      }
      assert(sum > 0);
    `
  }
];

/**
 * Run SSA transformation tests
 */
async function testSSA() {
  console.log('========================================');
  console.log('Running SSA transformation tests');
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
      
      // Transform to SSA
      console.log('\nTransforming to SSA...');
      const ssaProgram = transformToSSA(ast);
      console.log('✓ SSA transformation successful');

      // Format the SSA code
      console.log('\nFormatting SSA code...');
      const ssaCode = formatSSA(ssaProgram);
      console.log('✓ Formatting successful');

      console.log('\nSSA Form:');
      console.log(ssaCode);
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
testSSA().catch(console.error);

export default testSSA;
