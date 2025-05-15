/**
 * Test script focused on control flow (conditionals and loops)
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
 * Test conditional program
 */
async function testConditionalProgram() {
  console.log('\n=== Testing Conditional Program ===\n');
  
  try {
    // Read the example file
    const program = await readExampleFile('conditional-program.txt');
    
    console.log('Program:\n', program);
    
    // Parse the program
    const parseResult = await parserService.parseProgram(program);
    
    if (!parseResult.success) {
      console.error('Parse error:', parseResult.error);
      return;
    }
    
    console.log('\nParse result:', parseResult.success);
    console.log('AST:', JSON.stringify(parseResult.ast, null, 2));
    
    // Transform to SSA
    const ssaResult = await ssaService.transformToSSA(parseResult.ast, { loopUnrollDepth: 5 });
    
    if (!ssaResult.success) {
      console.error('SSA error:', ssaResult.error);
      return;
    }
    
    console.log('\nSSA result:', ssaResult.success);
    console.log('SSA AST:', JSON.stringify(ssaResult.ssaAst, null, 2));
    
    // Generate constraints
    const smtConstraints = await smtGenerationService.generateConstraints(
      ssaResult.ssaAst, 
      { loopUnrollDepth: 5 }
    );
    
    if (!smtConstraints.success) {
      console.error('SMT generation error:', smtConstraints.error);
      return;
    }
    
    console.log('\nSMT constraints:', smtConstraints.success);
    console.log('SMT script (preview):', smtConstraints.smtScript.substring(0, 500) + '...');
    
    // Check assertions
    const result = await z3Service.verifyAssertions(smtConstraints);
    
    console.log('\nVerification result:', result);
    
  } catch (error) {
    console.error('Error testing conditional program:', error.stack || error);
  }
}

/**
 * Test loop program
 */
async function testLoopProgram() {
  console.log('\n=== Testing Loop Program ===\n');
  
  try {
    // Read the example file
    const program = await readExampleFile('loop-program.txt');
    
    console.log('Program:\n', program);
    
    // Parse the program
    const parseResult = await parserService.parseProgram(program);
    
    if (!parseResult.success) {
      console.error('Parse error:', parseResult.error);
      return;
    }
    
    console.log('\nParse result:', parseResult.success);
    console.log('AST:', JSON.stringify(parseResult.ast, null, 2));
    
    // Transform to SSA
    const ssaResult = await ssaService.transformToSSA(parseResult.ast, { loopUnrollDepth: 5 });
    
    if (!ssaResult.success) {
      console.error('SSA error:', ssaResult.error);
      return;
    }
    
    console.log('\nSSA result:', ssaResult.success);
    console.log('SSA AST:', JSON.stringify(ssaResult.ssaAst, null, 2));
    
    // Generate constraints
    const smtConstraints = await smtGenerationService.generateConstraints(
      ssaResult.ssaAst, 
      { loopUnrollDepth: 5 }
    );
    
    if (!smtConstraints.success) {
      console.error('SMT generation error:', smtConstraints.error);
      return;
    }
    
    console.log('\nSMT constraints:', smtConstraints.success);
    console.log('SMT script (preview):', smtConstraints.smtScript.substring(0, 500) + '...');
    
    // Check assertions
    const result = await z3Service.verifyAssertions(smtConstraints);
    
    console.log('\nVerification result:', result);
    
  } catch (error) {
    console.error('Error testing loop program:', error.stack || error);
  }
}

/**
 * Run the tests
 */
async function runTests() {
  try {
    console.log('Starting control flow tests...');
    
    // Test conditional program
    await testConditionalProgram();
    
    // Test loop program
    await testLoopProgram();
    
    console.log('\nTests completed!');
  } catch (error) {
    console.error('Error running tests:', error.stack || error);
  }
}

// Run the tests
runTests().catch(error => console.error('Fatal error:', error.stack || error)); 