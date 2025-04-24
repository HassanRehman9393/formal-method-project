#!/usr/bin/env node
/**
 * Command-line test runner for SSA transformation
 */

// Use dynamic import for ES modules compatibility
async function runTests() {
  try {
    const { default: testSSA } = await import('./test-ssa.js');
    
    console.log('Running SSA transformation tests...');
    
    const { passedTests, failedTests } = await testSSA();
    
    // Set exit code based on test results
    process.exit(failedTests > 0 ? 1 : 0);
  } catch (error) {
    console.error('Error running tests:', error);
    process.exit(1);
  }
}

runTests();
