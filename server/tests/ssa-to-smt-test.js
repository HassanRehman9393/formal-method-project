const ssaToSmtTranslator = require('../src/services/ssaToSmtTranslator');
const smtLibGenerator = require('../src/services/smtLibGenerator');

/**
 * Test translating a simple SSA program to SMT
 */
async function testSimpleTranslation() {
  console.log('\n=== Testing Simple SSA to SMT Translation ===');
  
  // Create a simple SSA program
  const simpleSSA = {
    type: 'SSAProgram',
    blocks: [
      {
        label: 'entry',
        phiFunctions: [],
        instructions: [
          {
            type: 'Assignment',
            target: 'x_0',
            value: 5
          },
          {
            type: 'Assignment',
            target: 'y_0',
            value: {
              type: 'BinaryExpression',
              operator: '+',
              left: 'x_0',
              right: 3
            }
          },
          {
            type: 'Assert',
            condition: {
              type: 'BinaryExpression',
              operator: '>',
              left: 'y_0',
              right: 7
            }
          }
        ]
      }
    ]
  };
  
  try {
    // Translate SSA to SMT
    const result = ssaToSmtTranslator.translate(simpleSSA);
    
    console.log('Generated SMT constraints:');
    console.log(result.smtScript);
    
    return result.success;
  } catch (error) {
    console.error('Error in SSA to SMT translation test:', error);
    return false;
  }
}

/**
 * Test translating SSA with phi functions to SMT
 */
async function testPhiFunctionTranslation() {
  console.log('\n=== Testing Phi Function Translation to SMT ===');
  
  // Create an SSA program with phi functions
  const phiSSA = {
    type: 'SSAProgram',
    blocks: [
      {
        label: 'entry',
        phiFunctions: [],
        instructions: [
          {
            type: 'Assignment',
            target: 'x_0',
            value: 5
          }
        ],
        terminator: {
          type: 'Branch',
          condition: {
            type: 'BinaryExpression',
            operator: '>',
            left: 'x_0',
            right: 0
          },
          thenTarget: 'then',
          elseTarget: 'else'
        }
      },
      {
        label: 'then',
        phiFunctions: [],
        instructions: [
          {
            type: 'Assignment',
            target: 'y_0',
            value: 10
          }
        ],
        terminator: {
          type: 'Jump',
          target: 'join'
        }
      },
      {
        label: 'else',
        phiFunctions: [],
        instructions: [
          {
            type: 'Assignment',
            target: 'y_1',
            value: 20
          }
        ],
        terminator: {
          type: 'Jump',
          target: 'join'
        }
      },
      {
        label: 'join',
        phiFunctions: [
          {
            type: 'PhiFunction',
            variable: 'y',
            target: 'y_2',
            sources: ['0', '1']  // y_0 from 'then', y_1 from 'else'
          }
        ],
        instructions: [
          {
            type: 'Assert',
            condition: {
              type: 'BinaryExpression',
              operator: '>',
              left: 'y_2',
              right: 5
            }
          }
        ]
      }
    ]
  };
  
  try {
    // Translate SSA to SMT
    const result = ssaToSmtTranslator.translate(phiSSA);
    
    console.log('Generated SMT constraints with phi functions:');
    console.log(result.smtScript);
    
    return result.success;
  } catch (error) {
    console.error('Error in phi function translation test:', error);
    return false;
  }
}

/**
 * Test translating SSA with arrays to SMT
 */
async function testArrayTranslation() {
  console.log('\n=== Testing Array Translation to SMT ===');
  
  // Create an SSA program with array operations
  const arraySSA = {
    type: 'SSAProgram',
    blocks: [
      {
        label: 'entry',
        phiFunctions: [],
        instructions: [
          {
            type: 'Assignment',
            target: 'i_0',
            value: 0
          },
          {
            type: 'ArrayAssignment',
            array: 'arr_0',
            index: 'i_0',
            value: 42
          },
          {
            type: 'Assignment',
            target: 'x_0',
            value: {
              type: 'ArrayAccess',
              array: 'arr_0',
              index: 'i_0'
            }
          },
          {
            type: 'Assert',
            condition: {
              type: 'BinaryExpression',
              operator: '==',
              left: 'x_0',
              right: 42
            }
          }
        ]
      }
    ]
  };
  
  try {
    // Translate SSA to SMT
    const result = ssaToSmtTranslator.translate(arraySSA);
    
    console.log('Generated SMT constraints with arrays:');
    console.log(result.smtScript);
    
    return result.success;
  } catch (error) {
    console.error('Error in array translation test:', error);
    return false;
  }
}

/**
 * Run all tests
 */
async function runTests() {
  console.log('Starting SSA to SMT Translation tests...');
  
  const results = {
    simpleTranslation: await testSimpleTranslation(),
    phiFunctionTranslation: await testPhiFunctionTranslation(),
    arrayTranslation: await testArrayTranslation()
  };
  
  console.log('\n=== Test Results Summary ===');
  for (const [test, passed] of Object.entries(results)) {
    console.log(`- ${test}: ${passed ? 'PASSED' : 'FAILED'}`);
  }
  
  const allPassed = Object.values(results).every(result => result);
  console.log(`\nOverall: ${allPassed ? 'ALL TESTS PASSED' : 'SOME TESTS FAILED'}`);
}

// Run the tests
runTests()
  .then(() => console.log('Testing completed'))
  .catch(err => console.error('Error during testing:', err));
