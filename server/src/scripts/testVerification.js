#!/usr/bin/env node

/**
 * Test script for running verification end-to-end tests
 * Execute with: node testVerification.js [--verbose] [--fix]
 */

const { runEndToEndTests } = require('../tests/verificationEndToEnd');

// Parse command line arguments
const args = process.argv.slice(2);
const verbose = args.includes('--verbose');
const fixMode = args.includes('--fix');

// Set environment variables for testing
process.env.NODE_ENV = 'test';

async function runTests() {
  console.log('Starting verification system tests...');
  console.log('===============================');
  
  if (verbose) {
    console.log('Verbose mode enabled - showing detailed test output');
  }
  
  if (fixMode) {
    console.log('Fix mode enabled - attempting to fix issues automatically');
  }
  
  try {
    // Run the end-to-end tests
    const results = await runEndToEndTests({
      verbose,
      fix: fixMode
    });
    
    // Display detailed results if verbose
    if (verbose) {
      console.log('\nDetailed Test Results:');
      console.log('---------------------');
      
      results.details.forEach((detail, index) => {
        console.log(`${index + 1}. ${detail.name}: ${detail.status.toUpperCase()}`);
        console.log(`   ${detail.message}`);
        
        if (detail.error) {
          console.log(`   Error: ${detail.error}`);
        }
        
        console.log('');
      });
    }
    
    // Set exit code based on test results
    if (results.failed > 0) {
      console.log(`Tests completed with ${results.failed} failures.`);
      process.exit(1);
    } else {
      console.log('All tests passed successfully!');
      process.exit(0);
    }
  } catch (error) {
    console.error('Error running tests:', error);
    process.exit(1);
  }
}

// Run the tests
runTests(); 