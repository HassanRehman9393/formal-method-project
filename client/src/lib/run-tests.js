/**
 * Test runner for the parser, SSA transformation, and optimization components
 */

// ANSI color codes for test output formatting
const colors = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  cyan: '\x1b[36m'
};

// Initialize test tracking
let totalTests = 0;
let passedTests = 0;
let failedTests = 0;

// Start timing execution
const startTime = new Date().getTime();

// Banner
console.log(`${colors.bright}${colors.blue}=========================================${colors.reset}`);
console.log(`${colors.bright}${colors.blue}=== Formal Methods Analyzer Test Suite ===${colors.reset}`);
console.log(`${colors.bright}${colors.blue}=========================================${colors.reset}\n`);

// Intercept console output for tracking test results
const originalConsoleLog = console.log;
const originalConsoleError = console.error;

console.log = function(message, ...args) {
  originalConsoleLog(message, ...args);
  if (message && typeof message === 'string') {
    if (message.includes('✓')) {
      passedTests++;
      totalTests++;
    } else if (message.includes('❌')) {
      failedTests++;
      totalTests++;
    }
  }
};

// Run tests using dynamic imports for ES modules
async function runTests() {
  try {
    // Run parser tests
    console.log(`${colors.bright}${colors.cyan}Running Parser Tests...${colors.reset}\n`);
    await import('./parser/parser-test.js');
    console.log('\n');
  } catch (error) {
    console.error(`${colors.red}Error running parser tests: ${error.message}${colors.reset}`);
  }

  try {
    // Run SSA transformer tests
    console.log(`${colors.bright}${colors.cyan}Running SSA Transformer Tests...${colors.reset}\n`);
    await import('./ssa/ssa-test.js');
    console.log('\n');
  } catch (error) {
    console.error(`${colors.red}Error running SSA transformer tests: ${error.message}${colors.reset}`);
  }

  try {
    // Run SSA optimizer tests
    console.log(`${colors.bright}${colors.cyan}Running SSA Optimizer Tests...${colors.reset}\n`);
    await import('./optimizer/optimizer-test.js');
    console.log('\n');
  } catch (error) {
    console.error(`${colors.red}Error running SSA optimizer tests: ${error.message}${colors.reset}`);
  }

  try {
    // Run integration tests
    console.log(`${colors.bright}${colors.cyan}Running Integration Tests...${colors.reset}\n`);
    await import('./ssa/integration-test.js');
    console.log('\n');
  } catch (error) {
    console.error(`${colors.red}Error running integration tests: ${error.message}${colors.reset}`);
  }

  // Calculate time taken
  const endTime = new Date().getTime();
  const executionTime = (endTime - startTime) / 1000;

  // Restore original console methods
  console.log = originalConsoleLog;
  console.error = originalConsoleError;

  // Print summary
  console.log(`${colors.bright}${colors.blue}=============== Test Summary ===============${colors.reset}`);
  console.log(`${colors.bright}Total Tests: ${totalTests}${colors.reset}`);
  console.log(`${colors.bright}${colors.green}Passed: ${passedTests}${colors.reset}`);
  console.log(`${colors.bright}${colors.red}Failed: ${failedTests}${colors.reset}`);
  console.log(`${colors.bright}Execution Time: ${executionTime.toFixed(2)}s${colors.reset}`);
  console.log(`${colors.bright}${colors.blue}===========================================${colors.reset}\n`);

  // Exit with appropriate code
  process.exit(failedTests > 0 ? 1 : 0);
}

// Run the tests
runTests(); 