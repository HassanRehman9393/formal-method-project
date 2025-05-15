/**
 * Test script focused specifically on equivalence checking
 */
const fs = require('fs').promises;
const path = require('path');
const verificationService = require('./src/services/verificationService');
const smtGenerationService = require('./src/services/smtGenerationService');
const parserService = require('./src/services/parserService');
const ssaService = require('./src/services/ssaService');
const z3Service = require('./src/services/z3Service');

// Directory where examples are stored
const EXAMPLES_DIR = path.join(__dirname, '..', 'examples');

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
 * Test equivalence manually step by step
 */
async function testEquivalenceManually() {
  console.log('\n=== Testing Equivalence Manually ===\n');
  
  try {
    // Read the example files
    const program1 = await readExampleFile('program1.txt');
    const program2 = await readExampleFile('program2.txt');
    
    console.log('Program 1:\n', program1);
    console.log('Program 2:\n', program2);
    
    // Parse both programs
    const parseResult1 = await parserService.parseProgram(program1);
    const parseResult2 = await parserService.parseProgram(program2);
    
    if (!parseResult1.success || !parseResult2.success) {
      console.error('Parse error:', !parseResult1.success ? parseResult1.error : parseResult2.error);
      return;
    }
    
    console.log('Parse result 1 success:', parseResult1.success);
    console.log('Parse result 2 success:', parseResult2.success);
    
    // Transform to SSA
    const ssaResult1 = await ssaService.transformToSSA(parseResult1.ast, { loopUnrollDepth: 5 });
    const ssaResult2 = await ssaService.transformToSSA(parseResult2.ast, { loopUnrollDepth: 5 });
    
    if (!ssaResult1.success || !ssaResult2.success) {
      console.error('SSA error:', !ssaResult1.success ? ssaResult1.error : ssaResult2.error);
      return;
    }
    
    console.log('SSA result 1 success:', ssaResult1.success);
    console.log('SSA result 2 success:', ssaResult2.success);
    
    // Manually create constraints for equivalence check
    const constraints = {
      smtScript: `
        ;; Variables for Program 1
        (declare-const prog1_x Int)
        (declare-const prog1_y Int)
        (declare-const prog1_temp Int)
        (declare-const prog1_result Int)
        
        ;; Variables for Program 2
        (declare-const prog2_x Int)
        (declare-const prog2_y Int)
        (declare-const prog2_result Int)
        
        ;; Set up inputs to be identical
        (assert (= prog1_x 5))
        (assert (= prog1_y 10))
        (assert (= prog2_x 5))
        (assert (= prog2_y 10))
        
        ;; Program 1 logic
        (assert (= prog1_temp (+ prog1_x prog1_y)))
        (assert (= prog1_result prog1_temp))
        
        ;; Program 2 logic
        (assert (= prog2_result (+ prog2_x prog2_y)))
        
        ;; Check for inequality in results
        (assert (not (= prog1_result prog2_result)))
      `,
      variables: [
        'prog1_x', 'prog1_y', 'prog1_temp', 'prog1_result',
        'prog2_x', 'prog2_y', 'prog2_result'
      ]
    };
    
    // Check equivalence using Z3
    console.log('Manual SMT constraints:', constraints.smtScript);
    const result = await z3Service.checkEquivalence(constraints);
    
    console.log('Manual equivalence result:', JSON.stringify(result, null, 2));
    
    // Generate constraints using the standard approach
    console.log('Generate constraints using standard approach...');
    const constraintsResult = await smtGenerationService.generateConstraintsForEquivalence(
      ssaResult1.ssaAst,
      ssaResult2.ssaAst,
      { loopUnrollDepth: 5 }
    );
    
    if (constraintsResult.success) {
      console.log('Generated SMT script (full):', constraintsResult.smtScript);
      
      // Check equivalence using Z3 with the generated constraints
      console.log('Testing with generated constraints...');
      const generatedResult = await z3Service.checkEquivalence(constraintsResult);
      console.log('Generated result:', JSON.stringify(generatedResult, null, 2));
    } else {
      console.error('Failed to generate constraints:', constraintsResult.error);
    }
    
    // Test standard approach through API
    console.log('Testing standard API approach...');
    const apiResult = await verificationService.checkEquivalence(program1, program2, { loopUnrollDepth: 5 });
    console.log('Standard API result:', JSON.stringify(apiResult, null, 2));
    
  } catch (error) {
    console.error('Error in manual equivalence test:', error.stack || error);
  }
}

/**
 * Run the tests
 */
async function runTests() {
  try {
    console.log('Starting equivalence tests...');
    
    // Test equivalence manually
    await testEquivalenceManually();
    
    console.log('\nTests completed!');
  } catch (error) {
    console.error('Error running tests:', error.stack || error);
  }
}

// Run the tests
runTests().catch(error => console.error('Fatal error:', error.stack || error)); 