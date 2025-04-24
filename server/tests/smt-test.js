const smtGenerationService = require('../src/services/smtGenerationService');
const smtLibGenerator = require('../src/services/smtLibGenerator');

/**
 * Test basic SMT generation functionality
 */
async function testBasicSMT() {
  console.log('\n=== Testing Basic SMT Generation ===');
  
  // Test simple variable declaration
  const varDecl = smtLibGenerator.generateDeclaration('x', 'Int');
  console.log('Variable declaration:', varDecl);
  
  // Test assignment
  const assignment = smtLibGenerator.generateAssignment('x', 5);
  console.log('Assignment:', assignment);
  
  // Test arithmetic
  const addition = smtLibGenerator.generateArithmetic('+', 'x', 3);
  console.log('Addition:', addition);
  
  const multiplication = smtLibGenerator.generateArithmetic('*', 'x', 'y');
  console.log('Multiplication:', multiplication);
  
  // Test comparison
  const equality = smtLibGenerator.generateComparison('==', 'x', 'y');
  console.log('Equality:', equality);
  
  const lessThan = smtLibGenerator.generateComparison('<', 'x', 10);
  console.log('Less than:', lessThan);
  
  // Test logical operations
  const conjunction = smtLibGenerator.generateLogical('&&', 'p', 'q');
  console.log('Conjunction:', conjunction);
  
  const negation = smtLibGenerator.generateNot('p');
  console.log('Negation:', negation);
  
  // Test assertion
  const assertion = smtLibGenerator.generateAssertion(lessThan);
  console.log('Assertion:', assertion);
  
  return true;
}

/**
 * Test generating a complete SMT script
 */
async function testCompleteScript() {
  console.log('\n=== Testing Complete SMT Script Generation ===');
  
  const program = {
    variables: [
      { name: 'x', type: 'Int' },
      { name: 'y', type: 'Int' }
    ],
    assignments: [
      { name: 'x', value: 5 },
      { name: 'y', value: smtLibGenerator.generateArithmetic('+', 'x', 3) }
    ],
    assertions: [
      smtLibGenerator.generateComparison('>', 'y', 7)
    ]
  };
  
  const script = smtGenerationService.generateSMTScript(program);
  console.log('Generated SMT script:');
  console.log(script);
  
  return true;
}

/**
 * Test predefined examples
 */
async function testExamples() {
  console.log('\n=== Testing Predefined Examples ===');
  
  const examples = smtGenerationService.generateExamples();
  
  for (const [name, script] of Object.entries(examples)) {
    console.log(`\nExample: ${name}`);
    console.log(script);
  }
  
  return true;
}

/**
 * Test AST to SMT conversion
 */
async function testASTConversion() {
  console.log('\n=== Testing AST to SMT Conversion ===');
  
  // Mock AST for a simple program
  const mockAST = {
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
  
  try {
    const result = smtGenerationService.generateConstraints(mockAST);
    
    if (result.success) {
      console.log('Generated SMT script from AST:');
      console.log(result.smtScript);
      return true;
    } else {
      console.error('Failed to generate SMT from AST:', result.error);
      return false;
    }
  } catch (error) {
    console.error('Error testing AST conversion:', error);
    return false;
  }
}

/**
 * Run all tests
 */
async function runTests() {
  console.log('Starting SMT generation tests...');
  
  const results = {
    basicSMT: await testBasicSMT(),
    completeScript: await testCompleteScript(),
    examples: await testExamples(),
    astConversion: await testASTConversion()
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
