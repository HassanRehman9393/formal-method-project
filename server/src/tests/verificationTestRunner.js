/**
 * Verification Test Runner
 * Runs test cases against the verification pipeline and reports results
 */
const fs = require('fs').promises;
const path = require('path');
const { verificationService } = require('../services/index');
const parserService = require('../services/parserService');

class VerificationTestRunner {
  constructor() {
    this.testFilePath = path.join(__dirname, '../../../examples/verification-test-suite.txt');
    this.results = [];
  }

  /**
   * Extract individual test cases from test file
   * @returns {Array} Array of test case objects
   */
  async extractTestCases() {
    const content = await fs.readFile(this.testFilePath, 'utf8');
    const allLines = content.split('\n');
    
    const testCases = [];
    let currentTest = { name: '', code: [], expectedResult: '', description: '' };
    let capturing = false;
    
    for (let i = 0; i < allLines.length; i++) {
      const line = allLines[i];
      
      // Start of a new test case
      if (line.includes('===== Test Case')) {
        if (currentTest.code.length > 0) {
          testCases.push({ ...currentTest });
        }
        
        const testName = line.match(/Test Case \d+[A-Z]?:\s+(.*?)=/)[1].trim();
        currentTest = { 
          name: testName, 
          code: [], 
          expectedResult: '',
          description: ''
        };
        capturing = true;
      } 
      // Extract expected result
      else if (line.includes('Expected Result:')) {
        currentTest.expectedResult = line.includes('UNSAT') ? 'UNSAT' : 'SAT';
      }
      // Extract description
      else if (line.includes('Why:')) {
        currentTest.description = line.replace('// Why:', '').trim();
      }
      // Skip empty lines and pure comments at test boundaries
      else if (capturing && !line.trim().startsWith('//') && line.trim() !== '') {
        currentTest.code.push(line);
      }
    }
    
    // Add the last test if there is one
    if (currentTest.code.length > 0) {
      testCases.push({ ...currentTest });
    }
    
    return testCases;
  }
  
  /**
   * Run a single test case
   * @param {Object} testCase - Test case object
   * @returns {Object} Test result
   */
  async runTestCase(testCase) {
    try {
      console.log(`Running test: ${testCase.name}`);
      
      // Convert test code array to string
      const testCode = testCase.code.join('\n');
      
      // Parse program
      const parseResult = await parserService.parseProgram(testCode);
      if (!parseResult.success) {
        return {
          name: testCase.name,
          expected: testCase.expectedResult,
          actual: 'ERROR',
          passed: false,
          error: `Parse error: ${parseResult.error}`,
          description: testCase.description
        };
      }
      
      // Run verification with loop unrolling depth 5
      const verificationResult = await verificationService.verifyProgram(testCode, {
        loopUnrollDepth: 5,
        timeout: 15000, // 15-second timeout
        optimizeConstraints: true
      });
      
      // Check if verification result matches expectation
      const actual = verificationResult.verified ? 'UNSAT' : 'SAT';
      const passed = actual === testCase.expectedResult;
      
      return {
        name: testCase.name,
        expected: testCase.expectedResult,
        actual,
        passed,
        result: verificationResult,
        description: testCase.description
      };
    } catch (error) {
      console.error(`Error running test ${testCase.name}:`, error);
      return {
        name: testCase.name,
        expected: testCase.expectedResult,
        actual: 'ERROR',
        passed: false,
        error: error.message,
        description: testCase.description
      };
    }
  }
  
  /**
   * Format and display test results
   * @param {Array} results - Test results array
   */
  displayResults(results) {
    console.log('\n========== VERIFICATION TEST RESULTS ==========\n');
    
    let passCount = 0;
    let failCount = 0;
    
    results.forEach(result => {
      const status = result.passed ? '✅ PASS' : '❌ FAIL';
      if (result.passed) passCount++; else failCount++;
      
      console.log(`${status} | ${result.name}`);
      console.log(`       Expected: ${result.expected}`);
      console.log(`       Actual:   ${result.actual}`);
      console.log(`       Description: ${result.description}`);
      
      if (result.error) {
        console.log(`       Error: ${result.error}`);
      }
      
      // Display counterexample for failing verification
      if (result.result && result.result.counterexamples && result.result.counterexamples.length > 0) {
        console.log('       Counterexample:');
        const counterexample = result.result.counterexamples[0];
        
        // Safely display counterexample properties
        if (counterexample) {
          // Handle variables
          if (counterexample.variables) {
            console.log('           variables =', typeof counterexample.variables === 'object' ? 
                       'Variable values available' : counterexample.variables);
          }
          
          // Handle inputs
          if (counterexample.inputs) {
            console.log('           inputs =', typeof counterexample.inputs === 'object' ? 
                       'Input values available' : counterexample.inputs);
          }
          
          // Handle state
          if (counterexample.state) {
            console.log('           state =', typeof counterexample.state === 'object' ? 
                       'State values available' : counterexample.state);
          }
          
          // Handle failed assertion
          if (counterexample.failedAssertion) {
            console.log('           failedAssertion =', counterexample.failedAssertion);
          }
          
          // Handle arrays
          if (counterexample.arrays) {
            console.log('           arrays =', typeof counterexample.arrays === 'object' ? 
                       'Array values available' : counterexample.arrays);
          }
        } else {
          console.log('           (Counterexample details not available)');
        }
      }
      
      console.log('------------------------------------------');
    });
    
    console.log(`\nSummary: ${passCount} passed, ${failCount} failed, ${results.length} total`);
    console.log('\n==============================================\n');
  }
  
  /**
   * Run all tests
   */
  async runTests() {
    try {
      const testCases = await this.extractTestCases();
      console.log(`Found ${testCases.length} test cases`);
      
      const results = [];
      for (const testCase of testCases) {
        const result = await this.runTestCase(testCase);
        results.push(result);
      }
      
      this.displayResults(results);
      return results;
    } catch (error) {
      console.error('Error running tests:', error);
      return [];
    }
  }
}

/**
 * Run the tests if this file is executed directly
 */
if (require.main === module) {
  const runner = new VerificationTestRunner();
  runner.runTests()
    .then(() => {
      console.log('Test runner completed');
      process.exit(0);
    })
    .catch(error => {
      console.error('Test runner failed:', error);
      process.exit(1);
    });
}

module.exports = VerificationTestRunner; 