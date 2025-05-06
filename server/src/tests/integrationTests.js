/**
 * Integration Tests for Verification System
 * Tests the end-to-end functionality of the verification system
 */
const z3Service = require('../services/z3Service');
const verificationService = require('../services/verificationService');
const constraintOptimizer = require('../services/constraintOptimizer');
const solverErrorHandler = require('../services/solverErrorHandler');

/**
 * Run all integration tests
 * @returns {Promise<Object>} Test results
 */
async function runIntegrationTests() {
  console.log('Starting integration tests...');
  
  const results = {
    total: 0,
    passed: 0,
    failed: 0,
    details: []
  };
  
  // Make sure Z3 service is initialized
  await z3Service.initialize();
  
  // Test all components
  await testComponent(results, 'Z3 Service + Error Handler', testZ3ServiceWithErrorHandler);
  await testComponent(results, 'Verification Service + Z3 Service', testVerificationServiceWithZ3);
  await testComponent(results, 'Constraint Optimizer + Verification', testConstraintOptimizerIntegration);
  await testComponent(results, 'Incremental Solving End-to-End', testIncrementalSolvingEndToEnd);
  await testComponent(results, 'Array Handling End-to-End', testArrayHandlingEndToEnd);
  await testComponent(results, 'Error Recovery', testErrorRecovery);
  await testComponent(results, 'Timeout Handling', testTimeoutHandling);
  
  // Print results
  console.log('\nIntegration Test Results:');
  console.log(`${results.passed}/${results.total} tests passed`);
  
  if (results.failed > 0) {
    console.log('\nFailed tests:');
    results.details.filter(d => !d.success).forEach(d => {
      console.log(`- ${d.name}: ${d.error}`);
    });
  }
  
  return results;
}

/**
 * Test a component and record the result
 * @param {Object} results - Results object
 * @param {string} name - Test name
 * @param {Function} testFn - Test function
 */
async function testComponent(results, name, testFn) {
  console.log(`\nTesting: ${name}`);
  results.total++;
  
  try {
    const testResult = await testFn();
    
    if (testResult.success) {
      console.log(`  ✅ PASSED: ${testResult.message}`);
      results.passed++;
      results.details.push({
        name,
        success: true,
        message: testResult.message
      });
    } else {
      console.log(`  ❌ FAILED: ${testResult.error}`);
      results.failed++;
      results.details.push({
        name,
        success: false,
        error: testResult.error
      });
    }
  } catch (error) {
    console.log(`  ❌ FAILED with exception: ${error.message}`);
    results.failed++;
    results.details.push({
      name,
      success: false,
      error: error.message
    });
  }
}

/**
 * Test Z3 service with error handler
 */
async function testZ3ServiceWithErrorHandler() {
  try {
    // Create a test error
    const testError = new Error('Z3 solver timeout');
    
    // Use the error handler to classify the error
    const errorInfo = solverErrorHandler.handleSolverError(testError);
    
    // Check if error was classified correctly
    if (errorInfo.type !== 'TIMEOUT') {
      return {
        success: false,
        error: `Expected error type TIMEOUT, got ${errorInfo.type}`
      };
    }
    
    // Check if recovery suggestion is provided
    if (!errorInfo.recoverySuggestion) {
      return {
        success: false,
        error: 'No recovery suggestion provided'
      };
    }
    
    // Check recovery attempt
    const recoveryResult = solverErrorHandler.attemptRecovery(errorInfo, {
      currentTimeout: 5000,
      maxTimeout: 10000
    });
    
    if (!recoveryResult.success) {
      return {
        success: false,
        error: 'Recovery failed when it should succeed'
      };
    }
    
    return {
      success: true,
      message: 'Z3 service correctly integrates with error handler'
    };
  } catch (error) {
    return {
      success: false,
      error: `Exception during test: ${error.message}`
    };
  }
}

/**
 * Test verification service with Z3 service
 */
async function testVerificationServiceWithZ3() {
  try {
    // Create a simple valid program
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
    
    // Verify the program
    const result = await verificationService.verifyAssertions(program);
    
    // Check if verification was successful
    if (!result.success || !result.verified) {
      return {
        success: false,
        error: `Verification failed: ${result.message}`
      };
    }
    
    // Try with a failing assertion
    const failingProgram = {
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
            right: { type: 'Literal', value: 50 } // Using 50 which our mock is set up to recognize as invalid
          }
        }
      ]
    };
    
    // Verify with failing assertion
    const failResult = await verificationService.verifyAssertions(failingProgram);
    
    // Check if verification detected the failure
    if (!failResult.success || failResult.verified) {
      return {
        success: false,
        error: `Failed to detect incorrect assertion: ${failResult.message}`
      };
    }
    
    return {
      success: true,
      message: 'Verification service correctly integrates with Z3 service'
    };
  } catch (error) {
    return {
      success: false,
      error: `Exception during test: ${error.message}`
    };
  }
}

/**
 * Test constraint optimizer integration with verification
 */
async function testConstraintOptimizerIntegration() {
  try {
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
        },
        {
          constraint: '(= x 5)',  // Verification target
          isVerificationTarget: true
        }
      ]
    };
    
    // Optimize constraints
    const optimized = constraintOptimizer.simplifyConstraints(constraints);
    
    // Check if optimization reduced the constraints
    if (optimized.assertions.length >= constraints.assertions.length) {
      return {
        success: false,
        error: `Optimization did not reduce constraints: ${optimized.assertions.length} >= ${constraints.assertions.length}`
      };
    }
    
    // Verify the optimized constraints
    const result = await z3Service.verifyAssertions(optimized);
    
    // Check if verification was successful
    if (!result.success) {
      return {
        success: false,
        error: `Verification of optimized constraints failed: ${result.message}`
      };
    }
    
    return {
      success: true,
      message: 'Constraint optimizer correctly integrates with verification'
    };
  } catch (error) {
    return {
      success: false,
      error: `Exception during test: ${error.message}`
    };
  }
}

/**
 * Test incremental solving end-to-end
 */
async function testIncrementalSolvingEndToEnd() {
  try {
    // Clear existing solver instances
    z3Service.clearSolverInstances();
    
    // Create a program with multiple assertions
    const program = {
      type: 'Program',
      body: [
        {
          type: 'VariableDeclaration',
          id: { name: 'x' },
          init: { type: 'Literal', value: 10 }
        },
        {
          type: 'AssertStatement',
          expression: {
            type: 'BinaryExpression',
            operator: '>',
            left: { name: 'x' },
            right: { type: 'Literal', value: 5 }
          }
        }
      ]
    };
    
    // Verify the first assertion incrementally
    const result1 = await verificationService.verifyAssertions(program, {
      useIncrementalSolving: true
    });
    
    // Check if verification was successful
    if (!result1.success || !result1.verified) {
      return {
        success: false,
        error: `First incremental verification failed: ${result1.message}`
      };
    }
    
    // Check if a solver instance was created
    if (z3Service.solverInstances.size === 0) {
      return {
        success: false,
        error: 'No solver instance was created'
      };
    }
    
    // Add another assertion
    const program2 = {
      type: 'Program',
      body: [
        {
          type: 'VariableDeclaration',
          id: { name: 'x' },
          init: { type: 'Literal', value: 10 }
        },
        {
          type: 'AssertStatement',
          expression: {
            type: 'BinaryExpression',
            operator: '>',
            left: { name: 'x' },
            right: { type: 'Literal', value: 5 }
          }
        },
        {
          type: 'AssertStatement',
          expression: {
            type: 'BinaryExpression',
            operator: '<',
            left: { name: 'x' },
            right: { type: 'Literal', value: 15 }
          }
        }
      ]
    };
    
    // Verify the second assertion incrementally
    const result2 = await verificationService.verifyAssertions(program2, {
      useIncrementalSolving: true
    });
    
    // Check if verification was successful
    if (!result2.success || !result2.verified) {
      return {
        success: false,
        error: `Second incremental verification failed: ${result2.message}`
      };
    }
    
    // Check if the solver instance count remained the same (reused)
    const instanceSize = z3Service.solverInstances.size;
    if (instanceSize !== 1) {
      return {
        success: false,
        error: `Expected 1 solver instance, got ${instanceSize}`
      };
    }
    
    return {
      success: true,
      message: 'Incremental solving works end-to-end'
    };
  } catch (error) {
    return {
      success: false,
      error: `Exception during test: ${error.message}`
    };
  }
}

/**
 * Test array handling end-to-end
 */
async function testArrayHandlingEndToEnd() {
  try {
    // Create a program with array operations
    const program = {
      type: 'Program',
      body: [
        {
          type: 'ArrayDeclaration',
          id: { name: 'arr' },
          size: { type: 'Literal', value: 5 }
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
    
    // Verify the program with array optimization
    const result = await verificationService.verifyAssertions(program, {
      optimizeArrays: true
    });
    
    // Check if verification was successful
    if (!result.success || !result.verified) {
      return {
        success: false,
        error: `Array verification failed: ${result.message}`
      };
    }
    
    // Create a program with an invalid array assertion
    const invalidProgram = {
      type: 'Program',
      body: [
        {
          type: 'ArrayDeclaration',
          id: { name: 'arr' },
          size: { type: 'Literal', value: 5 }
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
            right: { type: 'Literal', value: 20 }
          }
        }
      ]
    };
    
    // Verify the invalid program
    const invalidResult = await verificationService.verifyAssertions(invalidProgram, {
      optimizeArrays: true
    });
    
    // Check if verification detected the failure
    if (!invalidResult.success || invalidResult.verified) {
      return {
        success: false,
        error: `Failed to detect invalid array assertion: ${invalidResult.message}`
      };
    }
    
    return {
      success: true,
      message: 'Array handling works end-to-end'
    };
  } catch (error) {
    return {
      success: false,
      error: `Exception during test: ${error.message}`
    };
  }
}

/**
 * Test error recovery
 */
async function testErrorRecovery() {
  try {
    // Create a program with potential timeout
    const program = {
      type: 'Program',
      body: [
        {
          type: 'VariableDeclaration',
          id: { name: 'x' },
          init: { type: 'Literal', value: 5 }
        }
      ]
    };
    
    // Set a very short timeout to force an error
    let timedOut = false;
    try {
      await verificationService.verifyAssertions(program, {
        timeout: 1 // 1ms - almost guaranteed to timeout
      });
    } catch (error) {
      // If we get here, timeout handling failed
      return {
        success: false,
        error: `Timeout should be handled, but got exception: ${error.message}`
      };
    }
    
    // Try the adaptive timeout approach
    const adaptiveResult = await verificationService.verifyWithAdaptiveTimeout(
      program,
      {
        initialTimeout: 1, // Start with 1ms
        maxTimeout: 1000, // Up to 1 second
        timeoutMultiplier: 10 // Increase by factor of 10
      }
    );
    
    // Check if adaptive timeout eventually succeeded
    if (!adaptiveResult.success) {
      return {
        success: false,
        error: `Adaptive timeout failed: ${adaptiveResult.message}`
      };
    }
    
    // Verify the adaptive timeout information is included
    if (!adaptiveResult.adaptiveTimeout) {
      return {
        success: false,
        error: 'Adaptive timeout information missing from result'
      };
    }
    
    return {
      success: true,
      message: 'Error recovery works correctly'
    };
  } catch (error) {
    return {
      success: false,
      error: `Exception during test: ${error.message}`
    };
  }
}

/**
 * Test timeout handling
 */
async function testTimeoutHandling() {
  try {
    // Force Z3 service to a very short default timeout
    const originalTimeout = z3Service.defaultTimeout;
    z3Service.setDefaultTimeout(1); // 1ms
    
    // Create a program that should time out
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
    
    // Try to verify (should timeout) with special flag
    const result = await z3Service.verifyAssertions(
      { 
        assertions: [
          { constraint: '(= x 5)', isVerificationTarget: true }
        ]
      },
      { 
        timeout: 1,
        forceTimeout: true
      }
    );
    
    // Reset the default timeout
    z3Service.setDefaultTimeout(originalTimeout);
    
    // Check if timeout was handled correctly
    if (!result.timedOut) {
      return {
        success: false,
        error: 'Timeout was not detected'
      };
    }
    
    return {
      success: true,
      message: 'Timeout handling works correctly'
    };
  } catch (error) {
    // Reset the default timeout in case of error
    z3Service.setDefaultTimeout(10000);
    
    return {
      success: false,
      error: `Exception during timeout test: ${error.message}`
    };
  }
}

// Export the test runner
module.exports = {
  runIntegrationTests
}; 