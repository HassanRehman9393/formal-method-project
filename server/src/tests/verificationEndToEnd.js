/**
 * End-to-End Test Utility for Verification System
 * Tests the full verification pipeline from parsing to solver integration
 */
const verificationService = require('../services/verificationService');
const z3Service = require('../services/z3Service');
const constraintOptimizer = require('../services/constraintOptimizer');

/**
 * Run a comprehensive test suite for the verification system
 * @param {Object} options - Test options
 * @returns {Object} Test results
 */
async function runEndToEndTests(options = {}) {
  console.log('Starting end-to-end verification tests...');
  
  const results = {
    total: 0,
    passed: 0,
    failed: 0,
    skipped: 0,
    details: []
  };
  
  try {
    // Test basic verification
    await runTest(results, 'Basic Verification', testBasicVerification);
    
    // Test with arrays
    await runTest(results, 'Array Verification', testArrayVerification);
    
    // Test timeout handling
    await runTest(results, 'Timeout Handling', testTimeoutHandling);
    
    // Test incremental solving
    await runTest(results, 'Incremental Solving', testIncrementalSolving);
    
    // Test constraint optimization
    await runTest(results, 'Constraint Optimization', testConstraintOptimization);
    
    // Test equivalence checking
    await runTest(results, 'Equivalence Checking', testEquivalenceChecking);
    
    // Test edge cases
    await runTest(results, 'Edge Cases', testEdgeCases);
    
    // Print summary
    console.log(`\nTest Summary: ${results.passed}/${results.total} passed, ${results.failed} failed, ${results.skipped} skipped`);
    
    return results;
  } catch (error) {
    console.error('Error in end-to-end tests:', error);
    return {
      ...results,
      error: error.message
    };
  }
}

/**
 * Run a single test and record results
 * @param {Object} results - Results object to update
 * @param {string} name - Test name
 * @param {Function} testFn - Test function
 */
async function runTest(results, name, testFn) {
  console.log(`\n----- Testing: ${name} -----`);
  results.total++;
  
  try {
    const testResult = await testFn();
    
    if (testResult.skip) {
      console.log(`SKIPPED: ${testResult.message || 'No reason provided'}`);
      results.skipped++;
      results.details.push({
        name,
        status: 'skipped',
        message: testResult.message
      });
      return;
    }
    
    if (testResult.success) {
      console.log(`PASSED: ${testResult.message || 'No details provided'}`);
      results.passed++;
      results.details.push({
        name,
        status: 'passed',
        message: testResult.message
      });
    } else {
      console.log(`FAILED: ${testResult.message || 'No details provided'}`);
      results.failed++;
      results.details.push({
        name,
        status: 'failed',
        message: testResult.message,
        error: testResult.error
      });
    }
  } catch (error) {
    console.error(`Error in test "${name}":`, error);
    results.failed++;
    results.details.push({
      name,
      status: 'error',
      message: 'Unexpected error during test',
      error: error.message
    });
  }
}

/**
 * Test basic verification functionality
 * @returns {Object} Test result
 */
async function testBasicVerification() {
  // Create a simple program with a valid assertion
  const validProgram = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { name: 'x' },
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'VariableDeclaration',
        id: { name: 'y' },
        init: { 
          type: 'BinaryExpression', 
          operator: '+',
          left: { name: 'x' },
          right: { type: 'Literal', value: 5 }
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '>',
          left: { name: 'y' },
          right: { type: 'Literal', value: 8 }
        }
      }
    ]
  };
  
  // Program with an invalid assertion
  const invalidProgram = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { name: 'x' },
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'VariableDeclaration',
        id: { name: 'y' },
        init: { 
          type: 'BinaryExpression', 
          operator: '+',
          left: { name: 'x' },
          right: { type: 'Literal', value: 3 }
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '>',
          left: { name: 'y' },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  // Verify both programs
  const validResult = await verificationService.verifyAssertions(validProgram);
  const invalidResult = await verificationService.verifyAssertions(invalidProgram);
  
  // Check results
  const validSuccess = validResult.success && validResult.verified;
  const invalidSuccess = invalidResult.success && !invalidResult.verified && 
                        invalidResult.counterexamples && 
                        invalidResult.counterexamples.length > 0;
  
  if (validSuccess && invalidSuccess) {
    return {
      success: true,
      message: 'Basic verification correctly identified valid and invalid assertions'
    };
  } else {
    return {
      success: false,
      message: 'Basic verification failed',
      error: `Valid program verification: ${validSuccess}, Invalid program verification: ${invalidSuccess}`
    };
  }
}

/**
 * Test array verification functionality
 * @returns {Object} Test result
 */
async function testArrayVerification() {
  // Create a program with array operations
  const program = {
    type: 'Program',
    body: [
      {
        type: 'ArrayDeclaration',
        id: { name: 'arr' },
        size: { type: 'Literal', value: 10 }
      },
      {
        type: 'AssignmentExpression',
        left: {
          type: 'MemberExpression',
          object: { name: 'arr' },
          property: { type: 'Literal', value: 0 }
        },
        right: { type: 'Literal', value: 10 }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '==',
          left: {
            type: 'MemberExpression',
            object: { name: 'arr' },
            property: { type: 'Literal', value: 0 }
          },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  // Verify the program
  const result = await verificationService.verifyAssertions(program);
  
  if (result.success && result.verified) {
    return {
      success: true,
      message: 'Array verification works correctly'
    };
  } else {
    return {
      success: false,
      message: 'Array verification failed',
      error: result.message || 'Unknown error'
    };
  }
}

/**
 * Test timeout handling
 * @returns {Object} Test result
 */
async function testTimeoutHandling() {
  // Create a simple constraints object for the test
  const constraints = {
    assertions: [
      { constraint: '(= x 5)', isVerificationTarget: true }
    ]
  };
  
  // Test directly with Z3Service using the forceTimeout flag
  const result = await z3Service.verifyAssertions(constraints, {
    timeout: 1,
    forceTimeout: true
  });
  
  if (result.success && result.timedOut) {
    return {
      success: true,
      message: 'Timeout handling works correctly'
    };
  } else {
    return {
      success: false,
      message: 'Timeout handling failed',
      error: result.timedOut ? 'Unknown error' : 'Timeout was not detected'
    };
  }
}

/**
 * Test incremental solving
 * @returns {Object} Test result
 */
async function testIncrementalSolving() {
  // Clear any existing solver instances
  z3Service.clearSolverInstances();
  
  // Create a basic program
  const program = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { name: 'x' },
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '==',
          left: { name: 'x' },
          right: { type: 'Literal', value: 5 }
        }
      }
    ]
  };
  
  // Verify once to create a solver instance
  await verificationService.verifyAssertions(program, {
    useIncrementalSolving: true
  });
  
  // Check if a solver instance was created
  const instanceCount = z3Service.solverInstances.size;
  
  // Verify again - should reuse the solver instance
  await verificationService.verifyAssertions(program, {
    useIncrementalSolving: true
  });
  
  // Check if the instance count remained the same
  const newInstanceCount = z3Service.solverInstances.size;
  
  if (instanceCount > 0 && instanceCount === newInstanceCount) {
    return {
      success: true,
      message: 'Incremental solving reuses solver instances correctly'
    };
  } else {
    return {
      success: false,
      message: 'Incremental solving failed',
      error: `Initial instance count: ${instanceCount}, New instance count: ${newInstanceCount}`
    };
  }
}

/**
 * Test constraint optimization
 * @returns {Object} Test result
 */
async function testConstraintOptimization() {
  // Create constraints with redundancies
  const constraints = {
    assertions: [
      {
        constraint: '(= x x)',
        isVerificationTarget: false
      },
      {
        constraint: '(= x 5)',
        isVerificationTarget: false
      },
      {
        constraint: '(= x 5)',  // Duplicate
        isVerificationTarget: false
      },
      {
        constraint: '(+ x 0)',  // Simplifiable
        isVerificationTarget: false
      }
    ]
  };
  
  // Optimize constraints
  const optimized = constraintOptimizer.simplifyConstraints(constraints);
  
  // Check if optimizations were applied
  const initialCount = constraints.assertions.length;
  const optimizedCount = optimized.assertions.length;
  
  if (optimizedCount < initialCount) {
    return {
      success: true,
      message: `Constraint optimization reduced assertions from ${initialCount} to ${optimizedCount}`
    };
  } else {
    return {
      success: false,
      message: 'Constraint optimization did not reduce assertions',
      error: `Initial count: ${initialCount}, Optimized count: ${optimizedCount}`
    };
  }
}

/**
 * Test equivalence checking
 * @returns {Object} Test result
 */
async function testEquivalenceChecking() {
  // Create two equivalent programs
  const program1 = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { name: 'x' },
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'VariableDeclaration',
        id: { name: 'result' },
        init: { 
          type: 'BinaryExpression', 
          operator: '+',
          left: { name: 'x' },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  const program2 = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { name: 'y' },  // Different variable name
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'VariableDeclaration',
        id: { name: 'result' },
        init: { 
          type: 'BinaryExpression', 
          operator: '+',
          left: { name: 'y' },  // Different variable
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  // Check equivalence
  const result = await verificationService.checkEquivalence(program1, program2);
  
  if (result.success && result.equivalent) {
    return {
      success: true,
      message: 'Equivalence checking correctly identified equivalent programs'
    };
  } else {
    return {
      success: false,
      message: 'Equivalence checking failed',
      error: result.message || 'Unknown error'
    };
  }
}

/**
 * Test edge cases in the solver
 * @returns {Object} Test result
 */
async function testEdgeCases() {
  const edgeCases = [
    // Test empty program
    {
      name: 'Empty Program',
      program: {
        type: 'Program',
        body: []
      }
    },
    
    // Test null assertions
    {
      name: 'Null Assertions',
      program: null
    },
    
    // Test very large integers
    {
      name: 'Large Integers',
      program: {
        type: 'Program',
        body: [
          {
            type: 'VariableDeclaration',
            id: { name: 'x' },
            init: { type: 'Literal', value: Number.MAX_SAFE_INTEGER }
          },
          {
            type: 'AssertStatement',
            expression: {
              type: 'BinaryExpression',
              operator: '>',
              left: { name: 'x' },
              right: { type: 'Literal', value: 0 }
            }
          }
        ]
      }
    },
    
    // Test with extreme timeouts
    {
      name: 'Zero Timeout',
      program: {
        type: 'Program',
        body: [
          {
            type: 'VariableDeclaration',
            id: { name: 'x' },
            init: { type: 'Literal', value: 5 }
          }
        ]
      },
      options: { timeout: 0 }
    },
    
    // Test with extremely large arrays
    {
      name: 'Large Array',
      program: {
        type: 'Program',
        body: [
          {
            type: 'ArrayDeclaration',
            id: { name: 'arr' },
            size: { type: 'Literal', value: 10000 }
          }
        ]
      }
    }
  ];
  
  // Track edge case results
  const edgeResults = [];
  
  // Run each edge case
  for (const test of edgeCases) {
    try {
      console.log(`Testing edge case: ${test.name}`);
      
      // Try to verify the program (expect it to complete without crashing)
      await verificationService.verifyAssertions(test.program, test.options);
      
      edgeResults.push({
        name: test.name,
        success: true
      });
    } catch (error) {
      edgeResults.push({
        name: test.name,
        success: false,
        error: error.message
      });
    }
  }
  
  // Check if all edge cases completed without crashing
  const failedEdgeCases = edgeResults.filter(r => !r.success);
  
  if (failedEdgeCases.length === 0) {
    return {
      success: true,
      message: `All ${edgeResults.length} edge cases handled without crashing`
    };
  } else {
    return {
      success: false,
      message: `${failedEdgeCases.length} edge cases failed`,
      error: failedEdgeCases.map(f => `${f.name}: ${f.error}`).join(', ')
    };
  }
}

module.exports = {
  runEndToEndTests
}; 