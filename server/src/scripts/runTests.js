#!/usr/bin/env node

/**
 * Test Runner Script
 * Runs all tests for the verification system
 */
const { runEndToEndTests } = require('../tests/verificationEndToEnd');
const { runIntegrationTests } = require('../tests/integrationTests');

// Set environment variables for testing
process.env.NODE_ENV = 'test';

// Parse command line arguments
const args = process.argv.slice(2);
const verbose = args.includes('--verbose');
const endToEndOnly = args.includes('--e2e-only');
const integrationOnly = args.includes('--integration-only');
const fixMode = args.includes('--fix');

async function runTests() {
  console.log('Starting verification system test suite...');
  console.log('========================================');
  
  // Track overall test results
  const results = {
    endToEnd: null,
    integration: null
  };
  
  // Run end-to-end tests unless integration-only flag is set
  if (!integrationOnly) {
    console.log('\n=== Running End-to-End Tests ===\n');
    results.endToEnd = await runEndToEndTests({
      verbose,
      fix: fixMode
    });
  }
  
  // Run integration tests unless e2e-only flag is set
  if (!endToEndOnly) {
    console.log('\n=== Running Integration Tests ===\n');
    results.integration = await runIntegrationTests();
  }
  
  // Print overall summary
  console.log('\n========================================');
  console.log('Test Summary:');
  
  let totalFailed = 0;
  
  if (results.endToEnd) {
    console.log(`End-to-End Tests: ${results.endToEnd.passed}/${results.endToEnd.total} passed, ${results.endToEnd.failed} failed, ${results.endToEnd.skipped} skipped`);
    totalFailed += results.endToEnd.failed;
  }
  
  if (results.integration) {
    console.log(`Integration Tests: ${results.integration.passed}/${results.integration.total} passed, ${results.integration.failed} failed`);
    totalFailed += results.integration.failed;
  }
  
  // Show detailed failure information if in verbose mode
  if (verbose && totalFailed > 0) {
    console.log('\nFailed Tests:');
    
    if (results.endToEnd && results.endToEnd.details) {
      const endToEndFailures = results.endToEnd.details.filter(d => d.status === 'failed' || d.status === 'error');
      if (endToEndFailures.length > 0) {
        console.log('\nEnd-to-End Test Failures:');
        endToEndFailures.forEach((failure, index) => {
          console.log(`${index + 1}. ${failure.name}`);
          console.log(`   Error: ${failure.error || failure.message}`);
        });
      }
    }
    
    if (results.integration && results.integration.details) {
      const integrationFailures = results.integration.details.filter(d => !d.success);
      if (integrationFailures.length > 0) {
        console.log('\nIntegration Test Failures:');
        integrationFailures.forEach((failure, index) => {
          console.log(`${index + 1}. ${failure.name}`);
          console.log(`   Error: ${failure.error}`);
        });
      }
    }
  }
  
  console.log('\nTests completed.');
  
  // Set exit code based on test results
  if (totalFailed > 0) {
    process.exit(1);
  } else {
    process.exit(0);
  }
}

// Run the tests
runTests().catch(error => {
  console.error('Error running tests:', error);
  process.exit(1);
}); 