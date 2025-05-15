/**
 * Verification Test Runner Script
 * 
 * This script runs the verification test suite against the mini-language programs
 * to validate the entire verification pipeline.
 */

// Set NODE_ENV to 'test' to enable test-specific behavior
process.env.NODE_ENV = 'test';

const VerificationTestRunner = require('./src/tests/verificationTestRunner');

/**
 * Main function that runs the tests
 */
async function main() {
  console.log('Starting Verification Test Runner...');
  
  try {
    // Create an instance of the test runner
    const runner = new VerificationTestRunner();
    
    // Run all tests
    const results = await runner.runTests();
    
    // Count failures to set exit code
    const failCount = results.filter(r => !r.passed).length;
    
    // Exit with appropriate code (0 for success, 1 for failures)
    process.exit(failCount > 0 ? 1 : 0);
  } catch (error) {
    console.error('Error running verification tests:', error);
    process.exit(1);
  }
}

// Run the main function
main().catch(error => {
  console.error('Unhandled error in main:', error);
  process.exit(1);
}); 