/**
 * Integration test for the parser and SSA transformation
 */

import { parseProgram } from '../parser/index.js';
import { transformToSSA, formatSSA, extractCFG } from './index.js';

/**
 * Tests the end-to-end flow from parsing to SSA generation
 */
async function testParserToSSA() {
  console.log('Running integration tests: Parser → SSA Transformation\n');
  
  // Sample complex program
  const programCode = `
    // Calculate factorial with an assertion
    n := 5;
    factorial := 1;
    i := 1;
    
    while (i <= n) {
      factorial := factorial * i;
      i := i + 1;
    }
    
    // Add an assertion to verify correctness
    assert(factorial == 120);
    
    // Test if statement and further assignments
    if (factorial > 100) {
      result := "large";
    } else {
      result := "small";
    }
  `;
  
  try {
    console.log('Source code:');
    console.log(programCode);
    
    console.log('\n1. Parsing code to AST...');
    const ast = parseProgram(programCode);
    console.log('✅ Parsing successful');
    
    console.log('\n2. Extracting control flow graph...');
    const cfg = extractCFG(ast);
    console.log('✅ CFG extraction successful');
    console.log(`   Generated ${cfg.nodes.length} CFG nodes`);
    
    console.log('\n3. Transforming to SSA...');
    const ssaProgram = transformToSSA(ast);
    console.log('✅ SSA transformation successful');
    
    console.log('\n4. Formatting SSA code...');
    const ssaCode = formatSSA(ssaProgram);
    console.log('✅ Formatting successful');
    
    console.log('\nSSA Form:');
    console.log(ssaCode);
    
    console.log('\n✅ All integration tests passed!');
    return true;
  } catch (error) {
    console.error('\n❌ Integration test failed:');
    console.error(error);
    return false;
  }
}

// Run the integration test when this module is executed directly
if (typeof require !== 'undefined' && require.main === module) {
  testParserToSSA().catch(console.error);
}

export default testParserToSSA;
