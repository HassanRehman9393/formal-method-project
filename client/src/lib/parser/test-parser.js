/**
 * Test script for the mini-language parser
 * Tests all language constructs implemented
 */

import { parse, ParseError } from './parser.js';
import util from 'util';

// Helper function to pretty-print ASTs
function prettyPrint(obj) {
  return util.inspect(obj, { depth: null, colors: true });
}

// Test cases for all language constructs
const testCases = [
  // Basic expressions and assignments
  { name: 'Simple assignment', code: 'x := 5;' },
  { name: 'Multiple assignments', code: 'x := 5;\ny := x + 3;' },
  { name: 'Arithmetic expressions', code: 'result := 2 + 3 * 4;' },
  { name: 'Boolean expressions', code: 'flag := x > 0 && y <= 10;' },
  { name: 'Array access assignment', code: 'arr[i] := 42;' },
  { name: 'Array access in expression', code: 'x := arr[i+1];' },
  
  // Control flow constructs
  { name: 'If statement', code: 'if (x > 0) { y := 1; }' },
  { name: 'If-else statement', code: 'if (x > 0) { y := 1; } else { y := -1; }' },
  { name: 'While loop', code: 'while (i < 10) { sum := sum + i; i := i + 1; }' },
  { name: 'For loop', code: 'for (i := 0; i < 10; i := i + 1) { sum := sum + i; }' },
  { name: 'Empty for loop parts', code: 'for (;;) { x := x + 1; }' },
  
  // Assertions
  { name: 'Assert statement', code: 'assert(x > 0);' },
  { name: 'Complex assertion', code: 'assert(x >= 0 && y == x * 2);' },
  
  // Blocks and empty statements
  { name: 'Block statement', code: '{ x := 1; y := 2; z := 3; }' },
  { name: 'Empty statement', code: ';' },
  
  // Combined constructs
  { name: 'Complex program', code: `
    sum := 0;
    for (i := 0; i < n; i := i + 1) {
      sum := sum + arr[i];
    }
    expected := (n * (n-1)) / 2;
    assert(sum == expected);
  `},
];

// Run tests
console.log('Running parser tests for all language constructs...\n');

let passCount = 0;
let failCount = 0;

for (const test of testCases) {
  console.log(`Test: ${test.name}`);
  console.log(`Code: ${test.code.trim()}`);
  
  try {
    const ast = parse(test.code);
    console.log('AST:', prettyPrint(ast));
    console.log('✅ PASS\n');
    passCount++;
  } catch (error) {
    console.log('❌ FAIL:', error instanceof ParseError ? error.getFormattedMessage() : error.message);
    failCount++;
  }
}

// Summary
console.log('=== Test Summary ===');
console.log(`Total: ${testCases.length}`);
console.log(`Passed: ${passCount}`);
console.log(`Failed: ${failCount}`);

if (failCount === 0) {
  console.log('\n🎉 All tests passed!');
} else {
  console.log('\n❌ Some tests failed.');
}
