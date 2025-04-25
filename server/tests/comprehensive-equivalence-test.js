/**
 * Comprehensive test suite for program equivalence checking
 */
const z3Service = require('../src/services/z3Service');
const equivalenceService = require('../src/services/equivalenceService');
const assert = require('assert').strict;

// Test suite configuration
const TEST_CONFIG = {
  verbose: true,         // Enable detailed output
  skipSlowTests: false,  // Skip tests that take a long time
  timeoutMs: 10000,      // Timeout in milliseconds
  runAllTests: true      // Run all tests or just the quick ones
};

/**
 * Run all tests
 */
async function runTests() {
  console.log('\n========== COMPREHENSIVE EQUIVALENCE TEST SUITE ==========');
  
  const testResults = {
    total: 0,
    passed: 0,
    failed: 0,
    skipped: 0
  };

  // Define all test cases
  const testCases = [
    { name: 'Basic Equivalence', fn: testBasicEquivalence },
    { name: 'Array Equivalence', fn: testArrayEquivalence },
    { name: 'Control Flow Equivalence', fn: testControlFlowEquivalence },
    { name: 'Loop Invariant', fn: testLoopInvariant, slow: true },
    { name: 'Boolean Expressions', fn: testBooleanExpressions },
    { name: 'Type Handling', fn: testTypeHandling },
    { name: 'Error Cases', fn: testErrorCases },
    { name: 'Edge Cases', fn: testEdgeCases, slow: true }
  ];
  
  // Run each test case
  for (const test of testCases) {
    // Skip slow tests if configured
    if (test.slow && TEST_CONFIG.skipSlowTests) {
      console.log(`\n[SKIPPED] ${test.name} (slow test)`);
      testResults.skipped++;
      continue;
    }
    
    testResults.total++;
    
    try {
      console.log(`\n----- Testing: ${test.name} -----`);
      const passed = await test.fn();
      
      if (passed) {
        console.log(`\n✅ ${test.name} test PASSED`);
        testResults.passed++;
      } else {
        console.log(`\n❌ ${test.name} test FAILED`);
        testResults.failed++;
      }
    } catch (error) {
      console.error(`\n❌ ${test.name} test ERROR:`, error);
      testResults.failed++;
    }
  }
  
  // Print test summary
  console.log('\n========== TEST SUMMARY ==========');
  console.log(`Total tests: ${testResults.total}`);
  console.log(`Passed: ${testResults.passed}`);
  console.log(`Failed: ${testResults.failed}`);
  console.log(`Skipped: ${testResults.skipped}`);
  console.log(`Success rate: ${Math.round((testResults.passed / testResults.total) * 100)}%`);
  
  return testResults.failed === 0;
}

//
// Individual Test Cases
//

/**
 * Test basic equivalence checking
 */
async function testBasicEquivalence() {
  console.log('Testing basic equivalence checking...');
  
  // Test 1: Two equivalent programs (x + y = y + x)
  const program1 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (+ x y))' }
    ],
    outputs: ['result']
  };
  
  const program2 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (+ y x))' }
    ],
    outputs: ['result']
  };
  
  // Test 2: Two non-equivalent programs (addition vs multiplication)
  const program3 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (* x y))' }
    ],
    outputs: ['result']
  };
  
  // Check equivalence for equivalent programs
  console.log('Checking equivalence of commutative addition...');
  const equivResult = await equivalenceService.checkEquivalence(program1, program2, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Equivalence result:', equivResult);
  }
  
  // Check equivalence for non-equivalent programs
  console.log('Checking equivalence of addition vs multiplication...');
  const inequivResult = await equivalenceService.checkEquivalence(program1, program3, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Inequivalence result:', inequivResult);
  }
  
  // Validate results
  const passedEquiv = equivResult.equivalent === true;
  const passedInequiv = inequivResult.equivalent === false;
  
  if (!passedEquiv) {
    console.error('❌ Equivalent programs were reported as not equivalent');
  }
  
  if (!passedInequiv) {
    console.error('❌ Non-equivalent programs were reported as equivalent');
  }
  
  return passedEquiv && passedInequiv;
}

/**
 * Test array equivalence checking
 */
async function testArrayEquivalence() {
  console.log('Testing array equivalence checking...');
  
  // Test 1: Two equivalent array programs
  const arrayProgram1 = {
    variables: ['x', 'i'],
    arrays: ['arr'],
    assertions: [
      { constraint: '(= (select arr i) x)' }
    ],
    outputs: ['arr']
  };
  
  const arrayProgram2 = {
    variables: ['x', 'i'],
    arrays: ['arr'],
    assertions: [
      { constraint: '(= (select arr i) x)' }
    ],
    outputs: ['arr']
  };
  
  // Test 2: Two non-equivalent array programs
  const arrayProgram3 = {
    variables: ['x', 'i'],
    arrays: ['arr'],
    assertions: [
      { constraint: '(= (select arr i) (+ x 1))' }
    ],
    outputs: ['arr']
  };
  
  // Check equivalence for equivalent array programs
  console.log('Checking equivalence of identical array programs...');
  const arrayEquivResult = await equivalenceService.checkEquivalence(arrayProgram1, arrayProgram2, {
    outputs: ['arr'],
    arrayOutputs: ['arr']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Array equivalence result:', arrayEquivResult);
  }
  
  // Check equivalence for non-equivalent array programs
  console.log('Checking equivalence of different array programs...');
  const arrayInequivResult = await equivalenceService.checkEquivalence(arrayProgram1, arrayProgram3, {
    outputs: ['arr'],
    arrayOutputs: ['arr']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Array inequivalence result:', arrayInequivResult);
  }
  
  // Validate results
  const passedEquiv = arrayEquivResult.equivalent === true;
  const passedInequiv = arrayInequivResult.equivalent === false;
  
  if (!passedEquiv) {
    console.error('❌ Equivalent array programs were reported as not equivalent');
  }
  
  if (!passedInequiv) {
    console.error('❌ Non-equivalent array programs were reported as equivalent');
  }
  
  return passedEquiv && passedInequiv;
}

/**
 * Test control flow equivalence checking
 */
async function testControlFlowEquivalence() {
  console.log('Testing control flow equivalence checking...');
  
  // Test 1: Two equivalent programs with different control flow
  const cfProgram1 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (ite (> x 0) x (* x -1)))' }
    ],
    outputs: ['result']
  };
  
  const cfProgram2 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (ite (< x 0) (* x -1) x))' }
    ],
    outputs: ['result']
  };
  
  // Test 2: Two non-equivalent programs with similar control flow
  const cfProgram3 = {
    variables: ['x', 'result'],
    assertions: [
      { constraint: '(= result (ite (> x 0) x 0))' }
    ],
    outputs: ['result']
  };
  
  // Check equivalence for equivalent programs with different control flow
  console.log('Checking equivalence of alternative implementations of abs(x)...');
  const cfEquivResult = await equivalenceService.checkEquivalence(cfProgram1, cfProgram2, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Control flow equivalence result:', cfEquivResult);
  }
  
  // Check equivalence for non-equivalent programs with similar control flow
  console.log('Checking equivalence of abs(x) vs max(x,0)...');
  const cfInequivResult = await equivalenceService.checkEquivalence(cfProgram1, cfProgram3, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Control flow inequivalence result:', cfInequivResult);
  }
  
  // Validate results
  const passedEquiv = cfEquivResult.equivalent === true;
  const passedInequiv = cfInequivResult.equivalent === false && cfInequivResult.counterexample;
  
  if (!passedEquiv) {
    console.error('❌ Equivalent control flow programs were reported as not equivalent');
  }
  
  if (!passedInequiv) {
    console.error('❌ Non-equivalent control flow programs were reported as equivalent');
  }
  
  return passedEquiv && passedInequiv;
}

/**
 * Test boolean expressions in equivalence checking
 */
async function testBooleanExpressions() {
  console.log('Testing boolean expression equivalence checking...');
  
  // Test 1: Two equivalent boolean expressions (De Morgan's law)
  const boolProgram1 = {
    variables: [
      { name: 'p', type: 'Bool' },
      { name: 'q', type: 'Bool' },
      { name: 'result', type: 'Bool' }
    ],
    assertions: [
      { constraint: '(= result (not (and p q)))' }
    ],
    outputs: ['result']
  };
  
  const boolProgram2 = {
    variables: [
      { name: 'p', type: 'Bool' },
      { name: 'q', type: 'Bool' },
      { name: 'result', type: 'Bool' }
    ],
    assertions: [
      { constraint: '(= result (or (not p) (not q)))' }
    ],
    outputs: ['result']
  };
  
  // Test 2: Two non-equivalent boolean expressions
  const boolProgram3 = {
    variables: [
      { name: 'p', type: 'Bool' },
      { name: 'q', type: 'Bool' },
      { name: 'result', type: 'Bool' }
    ],
    assertions: [
      { constraint: '(= result (not (or p q)))' }
    ],
    outputs: ['result']
  };
  
  // Check equivalence for De Morgan's law expressions
  console.log("Checking De Morgan's law: ¬(p ∧ q) ≡ (¬p ∨ ¬q)...");
  const boolEquivResult = await equivalenceService.checkEquivalence(boolProgram1, boolProgram2, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Boolean expression equivalence result:', boolEquivResult);
  }
  
  // Check equivalence for non-equivalent boolean expressions
  console.log("Checking ¬(p ∧ q) vs ¬(p ∨ q)...");
  const boolInequivResult = await equivalenceService.checkEquivalence(boolProgram1, boolProgram3, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Boolean expression inequivalence result:', boolInequivResult);
  }
  
  // Validate results
  const passedEquiv = boolEquivResult.equivalent === true;
  const passedInequiv = boolInequivResult.equivalent === false;
  
  if (!passedEquiv) {
    console.error('❌ Equivalent boolean expressions were reported as not equivalent');
  }
  
  if (!passedInequiv) {
    console.error('❌ Non-equivalent boolean expressions were reported as equivalent');
  }
  
  return passedEquiv && passedInequiv;
}

/**
 * Test type handling (integer vs. boolean vs. real)
 */
async function testTypeHandling() {
  console.log('Testing type handling in equivalence checking...');
  
  // Create programs with mixed variable types
  const typeProgram1 = {
    variables: [
      { name: 'x', type: 'Int' },
      { name: 'b', type: 'Bool' },
      { name: 'result', type: 'Int' }
    ],
    assertions: [
      { constraint: '(= result (ite b x 0))' }
    ],
    outputs: ['result']
  };
  
  const typeProgram2 = {
    variables: [
      { name: 'x', type: 'Int' },
      { name: 'b', type: 'Bool' },
      { name: 'result', type: 'Int' }
    ],
    assertions: [
      { constraint: '(= result (ite b x 0))' }
    ],
    outputs: ['result']
  };
  
  const typeProgram3 = {
    variables: [
      { name: 'x', type: 'Int' },
      { name: 'b', type: 'Bool' },
      { name: 'result', type: 'Int' }
    ],
    assertions: [
      { constraint: '(= result (ite b 0 x))' }
    ],
    outputs: ['result']
  };
  
  console.log('Checking equivalence of programs with mixed types...');
  const typeEquivResult = await equivalenceService.checkEquivalence(typeProgram1, typeProgram2, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Type handling equivalence result:', typeEquivResult);
  }
  
  console.log('Checking inequivalence of programs with mixed types...');
  const typeInequivResult = await equivalenceService.checkEquivalence(typeProgram1, typeProgram3, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Type handling inequivalence result:', typeInequivResult);
  }
  
  // Validate results
  const passedEquiv = typeEquivResult.equivalent === true;
  const passedInequiv = typeInequivResult.equivalent === false;
  
  if (!passedEquiv) {
    console.error('❌ Equivalent mixed-type programs were reported as not equivalent');
  }
  
  if (!passedInequiv) {
    console.error('❌ Non-equivalent mixed-type programs were reported as equivalent');
  }
  
  return passedEquiv && passedInequiv;
}

/**
 * Test error cases to ensure the system handles them gracefully
 */
async function testErrorCases() {
  console.log('Testing error handling in equivalence checking...');
  
  const validProgram = {
    variables: ['x', 'result'],
    assertions: [
      { constraint: '(= result x)' }
    ],
    outputs: ['result']
  };
  
  const invalidProgram = {
    variables: ['x', 'result'],
    assertions: [
      { constraint: '(= result (invalid x))' } // Invalid Z3 constraint
    ],
    outputs: ['result']
  };
  
  const emptyProgram = {
    variables: [],
    assertions: [],
    outputs: []
  };
  
  // Test 1: Valid vs. invalid program
  console.log('Testing valid vs. invalid program...');
  const invalidResult = await equivalenceService.checkEquivalence(validProgram, invalidProgram, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Invalid program result:', invalidResult);
  }
  
  // Test 2: Valid vs. empty program
  console.log('Testing valid vs. empty program...');
  const emptyResult = await equivalenceService.checkEquivalence(validProgram, emptyProgram, {
    outputs: ['result']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Empty program result:', emptyResult);
  }
  
  // Results should be defined, with no exceptions thrown
  const validInvalidHandled = invalidResult !== undefined;
  const validEmptyHandled = emptyResult !== undefined;
  
  return validInvalidHandled && validEmptyHandled;
}

/**
 * Test edge cases like timeout handling and large expressions
 */
async function testEdgeCases() {
  console.log('Testing edge cases in equivalence checking...');
  
  // Helper function to generate large expressions
  function generateLargeExpression(depth) {
    let expr = 'result';
    for (let i = 0; i < depth; i++) {
      expr = `(+ ${expr} (+ x y))`;
    }
    return `(= result ${expr})`;
  }
  
  // Test 1: Programs with very large expressions
  const largeProgram1 = {
    variables: ['x', 'y', 'z', 'result'],
    assertions: [
      { constraint: generateLargeExpression(10) } // Generate a large nested expression
    ],
    outputs: ['result']
  };
  
  const largeProgram2 = {
    variables: ['x', 'y', 'z', 'result'],
    assertions: [
      { constraint: generateLargeExpression(10) } // Generate the same large nested expression
    ],
    outputs: ['result']
  };
  
  // Test timeout handling
  console.log('Testing timeout handling...');
  const timeoutResult = await equivalenceService.checkEquivalence(largeProgram1, largeProgram2, {
    outputs: ['result'],
    timeoutMs: 500 // Very short timeout
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Timeout handling result:', timeoutResult);
  }
  
  // Test large expression handling
  console.log('Testing large expression handling...');
  const largeExprResult = await equivalenceService.checkEquivalence(largeProgram1, largeProgram2, {
    outputs: ['result'],
    timeoutMs: 5000
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Large expression handling result:', largeExprResult);
  }
  
  // Results should be defined, with no exceptions thrown
  const timeoutHandled = timeoutResult !== undefined;
  const largeExprHandled = largeExprResult !== undefined;
  
  return timeoutHandled && largeExprHandled;
}

/**
 * Test loop invariant handling
 */
async function testLoopInvariant() {
  console.log('Testing loop invariant handling...');
  
  // Two programs that compute the sum of numbers from 1 to n
  // First program uses loop (represented as an equation here)
  const loopProgram1 = {
    variables: ['n', 'sum'],
    assertions: [
      { constraint: '(= n 5)' },
      { constraint: '(= sum 15)' } // Sum of 1 to 5 is 15
    ],
    outputs: ['sum']
  };
  
  // Second program uses the mathematical formula n*(n+1)/2
  const loopProgram2 = {
    variables: ['n', 'sum'],
    assertions: [
      { constraint: '(= n 5)' },
      { constraint: '(= sum (* n (+ n 1) (div 1 2)))' } // Using the formula n*(n+1)/2
    ],
    outputs: ['sum']
  };
  
  // Third program computes a different sum
  const loopProgram3 = {
    variables: ['n', 'sum'],
    assertions: [
      { constraint: '(= n 5)' },
      { constraint: '(= sum (* n n))' } // n^2 instead of n*(n+1)/2
    ],
    outputs: ['sum']
  };
  
  console.log('Checking equivalence of loop-based sum and formula-based sum...');
  const loopEquivResult = await equivalenceService.checkEquivalence(loopProgram1, loopProgram2, {
    outputs: ['sum']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Loop equivalence result:', loopEquivResult);
  }
  
  console.log('Checking inequivalence with different formula...');
  const loopInequivResult = await equivalenceService.checkEquivalence(loopProgram1, loopProgram3, {
    outputs: ['sum']
  });
  
  if (TEST_CONFIG.verbose) {
    console.log('Loop inequivalence result:', loopInequivResult);
  }
  
  // In this specialized test, the results should reflect the equivalence of the loop sum
  // and formula, but the inequivalence with the incorrect formula
  const passedEquiv = loopEquivResult.equivalent === true;
  const passedInequiv = loopInequivResult.equivalent === false;
  
  return passedEquiv && passedInequiv;
}

// Main entry point
if (require.main === module) {
  runTests().catch(err => {
    console.error('Test suite failed with error:', err);
    process.exit(1);
  });
}

module.exports = { runTests };
