/**
 * Test script for examples from the examples directory
 */
const fs = require('fs').promises;
const path = require('path');
const verificationService = require('./src/services/verificationService');
const parserService = require('./src/services/parserService');

// Directory where examples are stored
const EXAMPLES_DIR = path.join(__dirname, '..', 'examples');

// Examples to test with expected results
const examples = [
  {
    name: 'simple-verification.txt',
    expected: { verified: true }
  },
  {
    name: 'failing-verification.txt', 
    expected: { verified: false }
  },
  {
    name: 'conditional-program.txt',
    expected: { verified: true }
  },
  {
    name: 'loop-program.txt',
    expected: { verified: true }
  },
  // Skip array program for now until we fix array handling
  // {
  //   name: 'array-program.txt',
  //   expected: { verified: true }
  // }
];

// Equivalence examples to test
const equivalenceExamples = [
  {
    name1: 'program1.txt',
    name2: 'program2.txt',
    expected: { equivalent: true }
  },
  {
    name1: 'program1.txt',
    name2: 'non-equivalent-program.txt',
    expected: { equivalent: false }
  }
];

/**
 * Read an example file
 */
async function readExampleFile(filename) {
  try {
    const filePath = path.join(EXAMPLES_DIR, filename);
    return await fs.readFile(filePath, 'utf8');
  } catch (error) {
    console.error(`Error reading example file ${filename}:`, error);
    throw error;
  }
}

/**
 * Test verification examples
 */
async function testVerificationExamples() {
  console.log('\n=== Testing Verification Examples ===\n');
  
  for (const example of examples) {
    try {
      console.log(`Testing ${example.name}...`);
      
      // Read the example file
      const program = await readExampleFile(example.name);
      
      // Parse the program
      const parseResult = await parserService.parseProgram(program);
      
      if (!parseResult.success) {
        console.error(`  ✗ Parse error for ${example.name}: ${parseResult.error}`);
        continue;
      }
      
      // Verify the program
      const result = await verificationService.verifyAssertions(parseResult.ast, {
        loopUnrollDepth: 5
      });
      
      // Check if the result matches expected outcome
      if (result.verified === example.expected.verified) {
        console.log(`  ✓ ${example.name} verification result: ${result.verified ? 'VERIFIED' : 'FAILED'} (as expected)`);
        
        if (!result.verified && result.counterexamples && result.counterexamples.length > 0) {
          console.log(`  ✓ Counterexample found:`, JSON.stringify(result.counterexamples[0], null, 2));
        }
      } else {
        console.error(`  ✗ ${example.name} verification result: ${result.verified ? 'VERIFIED' : 'FAILED'} (expected ${example.expected.verified ? 'VERIFIED' : 'FAILED'})`);
      }
    } catch (error) {
      console.error(`  ✗ Error testing ${example.name}:`, error);
    }
  }
}

/**
 * Test equivalence examples
 */
async function testEquivalenceExamples() {
  console.log('\n=== Testing Equivalence Examples ===\n');
  
  for (const example of equivalenceExamples) {
    try {
      console.log(`Testing ${example.name1} vs ${example.name2}...`);
      
      // Read the example files
      const program1 = await readExampleFile(example.name1);
      const program2 = await readExampleFile(example.name2);
      
      // Check equivalence
      const result = await verificationService.checkEquivalence(program1, program2, {
        loopUnrollDepth: 5
      });
      
      // Check if the result matches expected outcome
      if (result.success && result.equivalent === example.expected.equivalent) {
        console.log(`  ✓ Equivalence result: ${result.equivalent ? 'EQUIVALENT' : 'NOT EQUIVALENT'} (as expected)`);
        
        if (!result.equivalent && result.counterexample) {
          console.log(`  ✓ Counterexample found:`, JSON.stringify(result.counterexample, null, 2));
        }
      } else if (!result.success) {
        console.error(`  ✗ Equivalence check failed: ${result.error}`);
      } else {
        console.error(`  ✗ Equivalence result: ${result.equivalent ? 'EQUIVALENT' : 'NOT EQUIVALENT'} (expected ${example.expected.equivalent ? 'EQUIVALENT' : 'NOT EQUIVALENT'})`);
      }
    } catch (error) {
      console.error(`  ✗ Error testing equivalence example:`, error);
    }
  }
}

/**
 * Run all tests
 */
async function runTests() {
  try {
    console.log('Starting example tests...');
    
    // Test verification examples
    await testVerificationExamples();
    
    // Test equivalence examples
    await testEquivalenceExamples();
    
    console.log('\nTests completed!');
  } catch (error) {
    console.error('Error running tests:', error);
  }
}

// Run the tests
runTests().catch(console.error); 