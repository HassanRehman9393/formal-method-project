const axios = require('axios');
const fs = require('fs');
const path = require('path');

const API_BASE_URL = 'http://localhost:5000/api';

/**
 * Test the verification endpoint
 */
async function testVerifyEndpoint() {
  console.log('\n=== Testing /api/verify endpoint ===');
  
  const sampleProgram = `
    x := 5;
    y := 10;
    z := x + y;
    assert(z == 15);
  `;
  
  try {
    const response = await axios.post(`${API_BASE_URL}/verify`, {
      program: sampleProgram,
      loopUnrollingDepth: 3
    });
    
    console.log('Status:', response.status);
    console.log('Success:', response.data.success);
    console.log('Response data:', JSON.stringify(response.data, null, 2));
    return true;
  } catch (error) {
    console.error('Error testing verify endpoint:', error.message);
    if (error.response) {
      console.error('Response data:', error.response.data);
    }
    return false;
  }
}

/**
 * Test the equivalence checking endpoint
 */
async function testEquivalenceEndpoint() {
  console.log('\n=== Testing /api/equivalence endpoint ===');
  
  const program1 = `
    x := 10;
    y := 5;
    z := x - y;
  `;
  
  const program2 = `
    a := 10;
    b := 5;
    c := a - b;
  `;
  
  try {
    const response = await axios.post(`${API_BASE_URL}/equivalence`, {
      program1,
      program2,
      loopUnrollingDepth: 3
    });
    
    console.log('Status:', response.status);
    console.log('Success:', response.data.success);
    console.log('Response data:', JSON.stringify(response.data, null, 2));
    return true;
  } catch (error) {
    console.error('Error testing equivalence endpoint:', error.message);
    if (error.response) {
      console.error('Response data:', error.response.data);
    }
    return false;
  }
}

/**
 * Test the parse endpoint
 */
async function testParseEndpoint() {
  console.log('\n=== Testing /api/parse endpoint ===');
  
  const sampleProgram = `
    x := 5;
    if (x > 0) {
      y := x + 1;
    } else {
      y := x - 1;
    }
  `;
  
  try {
    const response = await axios.post(`${API_BASE_URL}/parse`, {
      program: sampleProgram
    });
    
    console.log('Status:', response.status);
    console.log('Success:', response.data.success);
    console.log('Response data:', JSON.stringify(response.data, null, 2));
    return true;
  } catch (error) {
    console.error('Error testing parse endpoint:', error.message);
    if (error.response) {
      console.error('Response data:', error.response.data);
    }
    return false;
  }
}

/**
 * Test invalid request handling
 */
async function testInvalidRequest() {
  console.log('\n=== Testing invalid requests handling ===');
  
  try {
    const response = await axios.post(`${API_BASE_URL}/verify`, {
      // Missing program field
      loopUnrollingDepth: 3
    });
    
    console.log('Status:', response.status);
    console.log('Unexpected success for invalid request');
    return false;
  } catch (error) {
    console.log('Expected error received for invalid request:', error.message);
    if (error.response) {
      console.log('Response data:', error.response.data);
    }
    return true;
  }
}

/**
 * Run all tests
 */
async function runTests() {
  console.log('Starting API tests...');
  
  const results = {
    verify: await testVerifyEndpoint(),
    equivalence: await testEquivalenceEndpoint(),
    parse: await testParseEndpoint(),
    invalidRequest: await testInvalidRequest(),
  };
  
  console.log('\n=== Test Results Summary ===');
  for (const [test, passed] of Object.entries(results)) {
    console.log(`- ${test}: ${passed ? 'PASSED' : 'FAILED'}`);
  }
  
  const allPassed = Object.values(results).every(result => result);
  console.log(`\nOverall: ${allPassed ? 'ALL TESTS PASSED' : 'SOME TESTS FAILED'}`);
}

// Run the tests
runTests()
  .then(() => console.log('Testing completed'))
  .catch(err => console.error('Error during testing:', err));
