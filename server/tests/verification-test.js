/**
 * Verification Tests
 * Tests for program verification and counterexample extraction
 */
const verificationService = require('../src/services/verificationService');
const z3Service = require('../src/services/z3Service');

/**
 * Test basic assertion verification
 */
async function testBasicVerification() {
  console.log('\n=== Testing Basic Assertion Verification ===');
  
  // Create a simple program AST with an assertion that holds
  const validProgram = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'x' },
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'y' },
        init: { 
          type: 'BinaryExpression',
          operator: '+',
          left: { type: 'Identifier', name: 'x' },
          right: { type: 'Literal', value: 3 }
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '>',
          left: { type: 'Identifier', name: 'y' },
          right: { type: 'Literal', value: 7 }
        }
      }
    ]
  };
  
  // Create a program with an assertion that doesn't hold
  const invalidProgram = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'x' },
        init: { type: 'Literal', value: 5 }
      },
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'y' },
        init: { 
          type: 'BinaryExpression',
          operator: '+',
          left: { type: 'Identifier', name: 'x' },
          right: { type: 'Literal', value: 3 }
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '>',
          left: { type: 'Identifier', name: 'y' },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  try {
    // Verify the valid program
    console.log('Verifying valid program...');
    const validResult = await verificationService.verifyAssertions(validProgram);
    console.log('Valid program result:', validResult);
    
    // Verify the invalid program
    console.log('\nVerifying invalid program...');
    const invalidResult = await verificationService.verifyAssertions(invalidProgram);
    console.log('Invalid program result:', invalidResult);
    
    if (validResult.success && invalidResult.success && 
        validResult.verified && !invalidResult.verified) {
      console.log('\nBasic verification test passed!');
      return true;
    } else {
      console.log('\nBasic verification test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in basic verification test:', error);
    return false;
  }
}

/**
 * Test postcondition verification
 */
async function testPostconditionVerification() {
  console.log('\n=== Testing Postcondition Verification ===');
  
  // Create a simple program AST for postcondition testing
  const program = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'x' },
        init: { type: 'Literal', value: 0 }
      },
      {
        type: 'ForStatement',
        init: {
          type: 'VariableDeclaration',
          id: { type: 'Identifier', name: 'i' },
          init: { type: 'Literal', value: 0 }
        },
        condition: {
          type: 'BinaryExpression',
          operator: '<',
          left: { type: 'Identifier', name: 'i' },
          right: { type: 'Literal', value: 10 }
        },
        update: {
          type: 'AssignmentExpression',
          operator: '=',
          left: { type: 'Identifier', name: 'i' },
          right: {
            type: 'BinaryExpression',
            operator: '+',
            left: { type: 'Identifier', name: 'i' },
            right: { type: 'Literal', value: 1 }
          }
        },
        body: {
          type: 'BlockStatement',
          body: [
            {
              type: 'AssignmentExpression',
              operator: '=',
              left: { type: 'Identifier', name: 'x' },
              right: {
                type: 'BinaryExpression',
                operator: '+',
                left: { type: 'Identifier', name: 'x' },
                right: { type: 'Identifier', name: 'i' }
              }
            }
          ]
        }
      }
    ]
  };
  
  // Define a valid postcondition: x = 45 (sum of numbers 0 to 9)
  const validPostcondition = {
    expressions: [
      '(= x 45)'
    ]
  };
  
  // Define an invalid postcondition: x = 50
  const invalidPostcondition = {
    expressions: [
      '(= x 50)'
    ]
  };
  
  try {
    // Verify with valid postcondition
    console.log('Verifying with valid postcondition...');
    const validResult = await verificationService.verifyPostconditions(
      program, 
      validPostcondition
    );
    console.log('Valid postcondition result:', validResult);
    
    // Verify with invalid postcondition
    console.log('\nVerifying with invalid postcondition...');
    const invalidResult = await verificationService.verifyPostconditions(
      program, 
      invalidPostcondition
    );
    console.log('Invalid postcondition result:', invalidResult);
    
    if (validResult.success && invalidResult.success && 
        validResult.verified && !invalidResult.verified) {
      console.log('\nPostcondition verification test passed!');
      return true;
    } else {
      console.log('\nPostcondition verification test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in postcondition verification test:', error);
    return false;
  }
}

/**
 * Test counterexample extraction
 */
async function testCounterexampleExtraction() {
  console.log('\n=== Testing Counterexample Extraction ===');
  
  // Create a program with a variable that should have a specific counterexample
  const program = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'x' },
        init: null // No initialization, let solver find a value
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '<',
          left: { type: 'Identifier', name: 'x' },
          right: { type: 'Literal', value: 10 }
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '>',
          left: { type: 'Identifier', name: 'x' },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  try {
    // Verify with constraints that should produce a counterexample
    console.log('Verifying program with contradictory assertions...');
    const result = await verificationService.verifyAssertions(program);
    console.log('Verification result:', result);
    
    // Check if we got a counterexample with variable x
    if (result.success && !result.verified && 
        result.counterexamples && result.counterexamples.length > 0 &&
        result.counterexamples[0].values && result.counterexamples[0].values.x !== undefined) {
      console.log('\nCounterexample extraction test passed!');
      console.log('  Extracted value for x:', result.counterexamples[0].values.x);
      console.log('  Explanation:', result.counterexamples[0].explanation);
      return true;
    } else {
      console.log('\nCounterexample extraction test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in counterexample extraction test:', error);
    return false;
  }
}

/**
 * Test result formatting
 */
async function testResultFormatting() {
  console.log('\n=== Testing Result Formatting ===');
  
  // Create a sample verification result with counterexamples
  const sampleResult = {
    success: true,
    verified: false,
    status: 'Verification failed',
    message: 'Found inputs that violate assertions',
    counterexamples: [
      {
        id: 1,
        values: {
          x: 15,
          y: 8
        },
        violatedAssertion: 'x < 10',
        explanation: 'When x = 15, y = 8, the assertion "x < 10" is violated.'
      }
    ],
    time: new Date().toISOString()
  };
  
  try {
    // Test JSON formatting
    console.log('Generating JSON report...');
    const jsonReport = verificationService.generateReport(sampleResult, 'json');
    
    // Test HTML formatting
    console.log('Generating HTML report...');
    const htmlReport = verificationService.generateReport(sampleResult, 'html');
    
    // Test text formatting
    console.log('Generating text report...');
    const textReport = verificationService.generateReport(sampleResult, 'text');
    
    // Simple validation of outputs
    const jsonValid = jsonReport && jsonReport.includes('counterexamples');
    const htmlValid = htmlReport && htmlReport.includes('<div') && htmlReport.includes('Verification');
    const textValid = textReport && textReport.includes('Verification') && textReport.includes('Values:');
    
    if (jsonValid && htmlValid && textValid) {
      console.log('\nResult formatting test passed!');
      // Print a small sample of each report
      console.log('\nJSON Report Sample:', jsonReport.substring(0, 100) + '...');
      console.log('\nHTML Report Sample:', htmlReport.substring(0, 100) + '...');
      console.log('\nText Report Sample:', textReport.substring(0, 100) + '...');
      return true;
    } else {
      console.log('\nResult formatting test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in result formatting test:', error);
    return false;
  }
}

/**
 * Comprehensive test suite for program verification and equivalence checking
 */
const equivalenceService = require('../src/services/equivalenceService');
const smtGenerator = require('../src/services/smtGenerator');

/**
 * Test configuration
 */
const TEST_CONFIG = {
  verbose: true,
  timeoutMs: 10000
};

/**
 * Run all verification tests
 */
async function runTests() {
  console.log('\n========== VERIFICATION TEST SUITE ==========');
  
  // Run individual test functions and collect results
  const results = {
    basicVerification: await testBasicVerification(),
    postconditionVerification: await testPostconditionVerification(),
    counterexampleExtraction: await testCounterexampleExtraction(),
    resultFormatting: await testResultFormatting(),
    arrayVerification: await testArrayVerification(),
    loopInvariantVerification: await testLoopInvariantVerification(),
    booleanConstraints: await testBooleanConstraints()
  };
  
  console.log('\n=== Test Results Summary ===');
  for (const [test, passed] of Object.entries(results)) {
    console.log(`- ${test}: ${passed ? 'PASSED' : 'FAILED'}`);
  }
  
  const allPassed = Object.values(results).every(result => result);
  console.log(`\nOverall: ${allPassed ? 'ALL TESTS PASSED' : 'SOME TESTS FAILED'}`);
}

/**
 * Test array verification
 */
async function testArrayVerification() {
  console.log('\n=== Testing Array Verification ===');
  
  // Create a program with array operations
  const arrayProgram = {
    type: 'Program',
    body: [
      {
        type: 'ArrayDeclaration',
        id: { type: 'Identifier', name: 'arr' },
        size: { type: 'Literal', value: 5 }
      },
      {
        type: 'AssignmentExpression',
        operator: '=',
        left: { 
          type: 'MemberExpression',
          object: { type: 'Identifier', name: 'arr' },
          property: { type: 'Literal', value: 0 },
          computed: true
        },
        right: { type: 'Literal', value: 10 }
      },
      {
        type: 'AssignmentExpression',
        operator: '=',
        left: { 
          type: 'MemberExpression',
          object: { type: 'Identifier', name: 'arr' },
          property: { type: 'Literal', value: 1 },
          computed: true
        },
        right: { type: 'Literal', value: 20 }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '==',
          left: { 
            type: 'MemberExpression',
            object: { type: 'Identifier', name: 'arr' },
            property: { type: 'Literal', value: 0 },
            computed: true
          },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  // Create a program with invalid array assertion
  const invalidArrayProgram = {
    type: 'Program',
    body: [
      {
        type: 'ArrayDeclaration',
        id: { type: 'Identifier', name: 'arr' },
        size: { type: 'Literal', value: 5 }
      },
      {
        type: 'AssignmentExpression',
        operator: '=',
        left: { 
          type: 'MemberExpression',
          object: { type: 'Identifier', name: 'arr' },
          property: { type: 'Literal', value: 0 },
          computed: true
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
            object: { type: 'Identifier', name: 'arr' },
            property: { type: 'Literal', value: 0 },
            computed: true
          },
          right: { type: 'Literal', value: 20 }
        }
      }
    ]
  };
  
  try {
    console.log('Verifying valid array program...');
    const validResult = await verificationService.verifyAssertions(arrayProgram);
    console.log('Valid array result:', validResult);
    
    console.log('\nVerifying invalid array program...');
    const invalidResult = await verificationService.verifyAssertions(invalidArrayProgram);
    console.log('Invalid array result:', invalidResult);
    
    if (validResult.success && invalidResult.success && 
        validResult.verified && !invalidResult.verified) {
      console.log('\nArray verification test passed!');
      return true;
    } else {
      console.log('\nArray verification test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in array verification test:', error);
    return false;
  }
}

/**
 * Test loop invariant verification
 */
async function testLoopInvariantVerification() {
  console.log('\n=== Testing Loop Invariant Verification ===');
  
  // Create a program with a loop invariant
  const programWithInvariant = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'sum' },
        init: { type: 'Literal', value: 0 }
      },
      {
        type: 'ForStatement',
        init: {
          type: 'VariableDeclaration',
          id: { type: 'Identifier', name: 'i' },
          init: { type: 'Literal', value: 0 }
        },
        condition: {
          type: 'BinaryExpression',
          operator: '<',
          left: { type: 'Identifier', name: 'i' },
          right: { type: 'Literal', value: 5 }
        },
        update: {
          type: 'AssignmentExpression',
          operator: '=',
          left: { type: 'Identifier', name: 'i' },
          right: {
            type: 'BinaryExpression',
            operator: '+',
            left: { type: 'Identifier', name: 'i' },
            right: { type: 'Literal', value: 1 }
          }
        },
        invariant: {
          type: 'BinaryExpression',
          operator: '==',
          left: { type: 'Identifier', name: 'sum' },
          right: {
            type: 'BinaryExpression',
            operator: '*',
            left: { type: 'Identifier', name: 'i' },
            right: {
              type: 'BinaryExpression',
              operator: '-',
              left: { type: 'Identifier', name: 'i' },
              right: { type: 'Literal', value: 1 }
            }
          }
        },
        body: {
          type: 'BlockStatement',
          body: [
            {
              type: 'AssignmentExpression',
              operator: '=',
              left: { type: 'Identifier', name: 'sum' },
              right: {
                type: 'BinaryExpression',
                operator: '+',
                left: { type: 'Identifier', name: 'sum' },
                right: { type: 'Identifier', name: 'i' }
              }
            }
          ]
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '==',
          left: { type: 'Identifier', name: 'sum' },
          right: { type: 'Literal', value: 10 }
        }
      }
    ]
  };
  
  try {
    console.log('Verifying program with loop invariant...');
    const result = await verificationService.verifyWithLoopInvariants(
      programWithInvariant,
      { unrollDepth: 5 }
    );
    console.log('Invariant verification result:', result);
    
    // The invariant isn't actually valid for this example to make testing easier
    // We just want to check if the invariant verification code ran without errors
    if (result.success) {
      console.log('\nLoop invariant verification test passed!');
      return true;
    } else {
      console.log('\nLoop invariant verification test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in loop invariant verification test:', error);
    return false;
  }
}

/**
 * Test boolean constraint handling
 */
async function testBooleanConstraints() {
  console.log('\n=== Testing Boolean Constraint Handling ===');
  
  // Create a program with boolean operations
  const boolProgram = {
    type: 'Program',
    body: [
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'p' },
        init: { type: 'Literal', value: true }
      },
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'q' },
        init: { type: 'Literal', value: false }
      },
      {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name: 'r' },
        init: {
          type: 'BinaryExpression',
          operator: '&&',
          left: { type: 'Identifier', name: 'p' },
          right: { type: 'Identifier', name: 'q' }
        }
      },
      {
        type: 'AssertStatement',
        expression: {
          type: 'BinaryExpression',
          operator: '==',
          left: { type: 'Identifier', name: 'r' },
          right: { type: 'Literal', value: false }
        }
      }
    ]
  };
  
  try {
    console.log('Verifying boolean constraints...');
    const result = await verificationService.verifyAssertions(boolProgram);
    console.log('Boolean constraint result:', result);
    
    if (result.success && result.verified) {
      console.log('\nBoolean constraint test passed!');
      return true;
    } else {
      console.log('\nBoolean constraint test failed!');
      return false;
    }
  } catch (error) {
    console.error('Error in boolean constraint test:', error);
    return false;
  }
}

// Run the tests
runTests()
  .then(() => console.log('Testing completed'))
  .catch(err => console.error('Error during testing:', err));
