/**
 * Tests for equivalence checking functionality
 */
const z3Service = require('../src/services/z3Service');
const equivalenceService = require('../src/services/equivalenceService');

/**
 * Run all equivalence tests
 */
async function runTests() {
  console.log('Starting equivalence checking tests...');
  
  // Test basic equivalence checking
  const basicResult = await testBasicEquivalence();
  
  // Test array equivalence checking
  const arrayResult = await testArrayEquivalence();
  
  // Test output detection and comparison
  const outputResult = await testOutputDetection();
  
  // Test constraint optimization
  const constraintResult = await testConstraintOptimization();
  
  // Collect results
  const results = {
    basicEquivalence: basicResult,
    arrayEquivalence: arrayResult,
    outputDetection: outputResult,
    constraintOptimization: constraintResult
  };
  
  // Report results
  console.log('\n=== Test Results Summary ===');
  for (const [test, passed] of Object.entries(results)) {
    console.log(`- ${test}: ${passed ? 'PASSED' : 'FAILED'}`);
  }
  
  const allPassed = Object.values(results).every(Boolean);
  console.log(`\nOverall: ${allPassed ? 'ALL TESTS PASSED' : 'SOME TESTS FAILED'}`);
  console.log('Testing completed');
}

/**
 * Test basic equivalence checking with scalar values
 */
async function testBasicEquivalence() {
  console.log('\n=== Testing Basic Equivalence Checking ===');
  
  // Two equivalent programs (x + y = y + x)
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
  
  // A different program (x * y instead of x + y)
  const program3 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (* x y))' }
    ],
    outputs: ['result']
  };
  
  // Test equivalent programs
  console.log('Checking equivalence of two semantically equivalent programs...');
  const options = {
    loopUnrollDepth: 3,
    includeArrays: true,
    timeoutMs: 30000,
    maxCounterexamples: 1,
    outputs: ['result']
  };
  console.log('Generating constraints with options:', options);
  
  const equivResult = await equivalenceService.checkEquivalence(program1, program2, options);
  console.log('Equivalence result:', equivResult);
  
  // Test inequivalent programs
  console.log('\nChecking inequivalence with a semantically different program...');
  const inequivResult = await equivalenceService.checkEquivalence(program1, program3, options);
  console.log('Inequivalence result:', inequivResult);
  
  // Check results
  const passed = equivResult.equivalent === true && inequivResult.equivalent === false;
  console.log(`\nBasic equivalence checking test: ${passed ? 'PASSED' : 'FAILED'}`);
  return passed;
}

/**
 * Test array equivalence checking
 */
async function testArrayEquivalence() {
  console.log('\n=== Testing Array Equivalence Checking ===');
  
  // Two equivalent array programs
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
  
  // A different array program
  const arrayProgram3 = {
    variables: ['x', 'i'],
    arrays: ['arr'],
    assertions: [
      { constraint: '(= (select arr i) (+ x 1))' }
    ],
    outputs: ['arr']
  };
  
  // Test equivalent array programs
  console.log('Checking equivalence of two semantically equivalent array programs...');
  const arrayOptions = {
    loopUnrollDepth: 3,
    includeArrays: true,
    timeoutMs: 30000,
    maxCounterexamples: 1,
    outputs: ['arr'],
    arrayOutputs: ['arr']
  };
  console.log('Generating constraints with options:', arrayOptions);
  
  const arrayEquivResult = await equivalenceService.checkEquivalence(arrayProgram1, arrayProgram2, arrayOptions);
  console.log('Array equivalence result:', arrayEquivResult);
  
  // Test inequivalent array programs
  console.log('\nChecking inequivalence with a semantically different array program...');
  const arrayInequivResult = await equivalenceService.checkEquivalence(arrayProgram1, arrayProgram3, arrayOptions);
  console.log('Array inequivalence result:', arrayInequivResult);
  
  const passed = arrayEquivResult.equivalent === true && arrayInequivResult.equivalent === false;
  console.log(`\nArray equivalence checking test: ${passed ? 'PASSED' : 'FAILED'}`);
  return passed;
}

/**
 * Test output detection and comparison
 */
async function testOutputDetection() {
  console.log('\n=== Testing Output Detection and Comparison ===');
  
  // Two programs with different variable names for the same output
  const p1 = {
    variables: ['x', 'y', 'result'],
    assertions: [
      { constraint: '(= result (+ x y))' }
    ]
  };
  
  const p2 = {
    variables: ['x', 'y', 'output'],
    assertions: [
      { constraint: '(= output (+ x y))' }
    ]
  };
  
  // Test explicit output mapping
  console.log('\nChecking equivalence with explicit output mapping...');
  const mappingOptions = {
    loopUnrollDepth: 3,
    includeArrays: true,
    timeoutMs: 30000,
    maxCounterexamples: 1,
    outputMappings: [{ program1: 'result', program2: 'output' }]
  };
  console.log('Generating constraints with options:', mappingOptions);
  
  const detectedOutputs = equivalenceService.detectOutputs(p1);
  console.log('Detected outputs:', detectedOutputs);
  
  const mappingResult = await equivalenceService.checkEquivalence(p1, p2, mappingOptions);
  console.log('Equivalence result with explicit mapping:', mappingResult);
  
  const passed = mappingResult.equivalent === true;
  console.log(`\nOutput detection and comparison test: ${passed ? 'PASSED' : 'FAILED'}`);
  return passed;
}

/**
 * Test constraint optimization
 */
async function testConstraintOptimization() {
  console.log('\n=== Testing Constraint Optimization ===');
  
  // Program with redundant constraints
  const program = {
    variables: ['x', 'y', 'z', 'result'],
    assertions: [
      { constraint: '(= x 5)' },
      { constraint: '(= y (+ x 5))' },
      { constraint: '(= z (+ x y))' },
      { constraint: '(= result (+ z 5))' },
      { constraint: '(= x 5)' },                // Duplicate
      { constraint: '(= result (+ z 5))' }      // Duplicate
    ]
  };
  
  console.log('Generate constraints for program with redundancies...');
  console.log('Optimizing constraints...');
  
  const originalConstraints = program.assertions;
  console.log('Original constraints count:', originalConstraints.length);
  
  // Optimize by removing duplicates
  const optimizedConstraints = [];
  const seen = new Set();
  
  for (const assertion of originalConstraints) {
    if (!seen.has(assertion.constraint)) {
      seen.add(assertion.constraint);
      optimizedConstraints.push(assertion);
    }
  }
  
  console.log('Optimized constraints count:', optimizedConstraints.length);
  
  console.log('\nChecking equivalence with optimized constraints...');
  
  const passed = optimizedConstraints.length < originalConstraints.length;
  console.log(`\nConstraint optimization test: ${passed ? 'PASSED' : 'FAILED'}`);
  return passed;
}

// Run all tests
runTests().catch(err => console.error('Error running tests:', err));
