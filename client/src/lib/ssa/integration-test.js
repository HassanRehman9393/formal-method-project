/**
 * Integration tests for the complete pipeline:
 * Parsing -> SSA Transformation -> Optimization
 */

import { parse } from '../parser/parser.js';
import { transformToSSA } from './ssaTransformer.js';
import { optimizeSSA } from '../optimizer/optimizationPipeline.js';

// Track test results
let passedTests = 0;
let failedTests = 0;

/**
 * Run an integration test through the entire pipeline
 * 
 * @param {string} name - Test name
 * @param {string} code - Program code
 * @param {Object} options - Test options
 * @param {Object} expectations - Expected test results
 */
function runTest(name, code, options = {}, expectations = {}) {
  console.log(`Running integration test: ${name}`);
  try {
    // Parse the program
    const ast = parse(code);
    if (!ast) {
      throw new Error('Parser returned null or undefined');
    }
    
    // Transform to SSA
    const ssaResult = transformToSSA(ast, options);
    if (!ssaResult || !ssaResult.ssaAST) {
      throw new Error('SSA transformation returned invalid result');
    }
    
    // Optimize SSA
    const optimizedResult = optimizeSSA(ssaResult);
    if (!optimizedResult) {
      throw new Error('SSA optimization returned invalid result');
    }
    
    // Verify expectations if provided
    if (expectations.optimizations && expectations.optimizations.length > 0) {
      const optimizationsMade = optimizedResult.optimizationsMade || [];
      for (const expected of expectations.optimizations) {
        if (!optimizationsMade.some(opt => opt.type === expected)) {
          console.error(`❌ Expected optimization "${expected}" was not applied`);
          failedTests++;
          return;
        }
      }
    }
    
    console.log(`✓ Integration test "${name}" passed`);
    passedTests++;
  } catch (error) {
    console.error(`❌ Integration test "${name}" failed with error: ${error.message}`);
    failedTests++;
  }
}

// Run the tests

console.log('\n=== Basic Integration Tests ===');

// Test 1: Simple program with constant propagation
runTest(
  'Simple constant propagation',
  `
    x := 5;
    y := 10;
    z := x + y;
    result := z * 2;
  `,
  { loopUnrollDepth: 3 },
  { optimizations: ['ConstantPropagation'] }
);

// Test 2: Conditional with dead code elimination
runTest(
  'Conditional with dead code',
  `
    flag := true;
    if (flag) {
      x := 10;
      result := x * 2;
    } else {
      // This branch should be eliminated
      x := 20;
      result := x * 3;
    }
    unused := 42; // This should be eliminated
  `,
  { loopUnrollDepth: 3 },
  { optimizations: ['ConstantPropagation', 'DeadCodeElimination'] }
);

// Test 3: Loop unrolling and optimization
runTest(
  'Loop unrolling with optimization',
  `
    sum := 0;
    for (i := 0; i < 3; i := i + 1) {
      temp := i * 2;
      sum := sum + temp;
    }
    result := sum;
  `,
  { loopUnrollDepth: 3 },
  { optimizations: ['ConstantPropagation'] }
);

// Test 4: Array access
runTest(
  'Array access patterns',
  `
    arr[0] := 1;
    arr[1] := 2;
    arr[2] := 3;
    sum := arr[0] + arr[1] + arr[2];
    result := sum;
  `,
  { loopUnrollDepth: 3 },
  { optimizations: ['ConstantPropagation'] }
);

// Test 5: Complex expressions
runTest(
  'Complex expressions',
  `
    a := 5;
    b := 10;
    c := 15;
    
    result := (a + b) * c / (a + b - 5);
  `,
  { loopUnrollDepth: 3 },
  { optimizations: ['ConstantPropagation'] }
);

// Report summary
console.log('\n=== Integration Test Summary ===');
console.log(`Passed: ${passedTests}`);
console.log(`Failed: ${failedTests}`);
console.log('All integration tests completed.\n');
