/**
 * Test script for edge cases in the mini-language parser
 * This tests specific edge cases like nested arrays and chained assignments
 */

import { parseProgram } from './index.js';
import util from 'util';

// Helper function to pretty-print ASTs
function prettyPrint(obj) {
  return util.inspect(obj, { depth: null, colors: true });
}

// Test cases for specific edge cases
const testCases = [
  // Nested array access
  { name: 'Nested array access', code: 'matrix[i][j] := i*j;' },
  
  // Chained assignments
  { name: 'Chained assignments', code: 'x := y := z := 10;' },
  
  // Combined edge cases
  { name: 'Complex array access with expressions', code: 'matrix[i+1][j*2] := matrix[i][j] + 5;' },
  
  // Multiple nested array access levels
  { name: 'Three-level nested array', code: 'cube[x][y][z] := 1;' },
  
  // Chained assignments with expressions
  { name: 'Chained assignments with expressions', code: 'a := b := c := x + y * z;' }
];

// Run tests
console.log('Running parser edge case tests...\n');

let passCount = 0;
let failCount = 0;

for (const test of testCases) {
  console.log(`Test: ${test.name}`);
  console.log(`Code: ${test.code.trim()}`);
  
  try {
    const ast = parseProgram(test.code);
    console.log('AST:', prettyPrint(ast));
    console.log('✅ PASS\n');
    passCount++;
  } catch (error) {
    console.log('❌ FAIL:', error.message);
    console.log('');
    failCount++;
  }
}

// Summary
console.log('=== Test Summary ===');
console.log(`Total: ${testCases.length}`);
console.log(`Passed: ${passCount}`);
console.log(`Failed: ${failCount}`);

if (failCount === 0) {
  console.log('\n🎉 All edge case tests passed!');
} else {
  console.log('\n❌ Some edge case tests failed.');
}
