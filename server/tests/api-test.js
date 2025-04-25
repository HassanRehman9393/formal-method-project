const http = require('http');

// Configuration
const CONFIG = {
  host: 'localhost',
  port: 3001,
  timeoutMs: 10000
};

/**
 * Make an HTTP request to the API
 * @param {string} method - HTTP method (GET, POST, etc.)
 * @param {string} path - API endpoint path
 * @param {Object} body - Request body (for POST requests)
 * @returns {Promise<Object>} Response data
 */
function makeRequest(method, path, body = null) {
  return new Promise((resolve, reject) => {
    const options = {
      hostname: CONFIG.host,
      port: CONFIG.port,
      path,
      method,
      headers: {
        'Content-Type': 'application/json'
      }
    };

    const req = http.request(options, (res) => {
      let data = '';
      res.on('data', (chunk) => {
        data += chunk;
      });

      res.on('end', () => {
        try {
          const parsedData = JSON.parse(data);
          resolve({
            statusCode: res.statusCode,
            data: parsedData
          });
        } catch (error) {
          resolve({
            statusCode: res.statusCode,
            data: data
          });
        }
      });
    });

    req.on('error', (error) => {
      reject(error);
    });

    // Set a timeout
    req.setTimeout(CONFIG.timeoutMs, () => {
      req.abort();
      reject(new Error(`Request timeout after ${CONFIG.timeoutMs}ms`));
    });

    if (body) {
      req.write(JSON.stringify(body));
    }
    req.end();
  });
}

/**
 * Test the /api/verify endpoint
 */
async function testVerifyEndpoint() {
  console.log('=== Testing /api/verify endpoint ===');
  
  try {
    // Simple program with a valid assertion
    const validProgram = {
      program: `
        x := 5;
        y := 10;
        z := x + y;
        assert(z == 15);
      `,
      options: {
        loopUnrollDepth: 3
      }
    };
    
    const validResponse = await makeRequest('POST', '/api/verify', validProgram);
    console.log('Valid program verification response:', validResponse);
    
    // Program with an invalid assertion
    const invalidProgram = {
      program: `
        x := 5;
        y := 10;
        z := x + y;
        assert(z == 16); // This should fail
      `,
      options: {
        loopUnrollDepth: 3
      }
    };
    
    const invalidResponse = await makeRequest('POST', '/api/verify', invalidProgram);
    console.log('Invalid program verification response:', invalidResponse);
    
    return validResponse.statusCode === 200 && 
           validResponse.data.success && 
           invalidResponse.statusCode === 200 && 
           invalidResponse.data.success && 
           !invalidResponse.data.verified;
  } catch (error) {
    console.log('Error testing verify endpoint:', error.message);
    return false;
  }
}

/**
 * Test the /api/equivalence endpoint
 */
async function testEquivalenceEndpoint() {
  console.log('\n=== Testing /api/equivalence endpoint ===');
  
  try {
    // Two equivalent programs
    const equivalentPrograms = {
      program1: {
        variables: ['x', 'y', 'result'],
        assertions: [
          { constraint: '(= result (+ x y))' }
        ]
      },
      program2: {
        variables: ['x', 'y', 'result'],
        assertions: [
          { constraint: '(= result (+ y x))' }
        ]
      },
      options: {
        outputs: ['result']
      }
    };
    
    const equivalentResponse = await makeRequest('POST', '/api/equivalence/check', equivalentPrograms);
    console.log('Equivalent programs response:', equivalentResponse);
    
    // Two non-equivalent programs
    const nonEquivalentPrograms = {
      program1: {
        variables: ['x', 'y', 'result'],
        assertions: [
          { constraint: '(= result (+ x y))' }
        ]
      },
      program2: {
        variables: ['x', 'y', 'result'],
        assertions: [
          { constraint: '(= result (* x y))' }
        ]
      },
      options: {
        outputs: ['result']
      }
    };
    
    const nonEquivalentResponse = await makeRequest('POST', '/api/equivalence/check', nonEquivalentPrograms);
    console.log('Non-equivalent programs response:', nonEquivalentResponse);
    
    return equivalentResponse.statusCode === 200 && 
           nonEquivalentResponse.statusCode === 200 && 
           equivalentResponse.data.success && 
           nonEquivalentResponse.data.success && 
           equivalentResponse.data.equivalent && 
           !nonEquivalentResponse.data.equivalent;
  } catch (error) {
    console.log('Error testing equivalence endpoint:', error.message);
    return false;
  }
}

/**
 * Test the /api/parse endpoint
 */
async function testParseEndpoint() {
  console.log('\n=== Testing /api/parse endpoint ===');
  
  try {
    // Simple program to parse
    const parseRequest = {
      programCode: `
        x := 5;
        y := 10;
        z := x + y;
        assert(z == 15);
      `
    };
    
    const parseResponse = await makeRequest('POST', '/api/parse', parseRequest);
    console.log('Parse response:', parseResponse);
    
    // Validate syntax
    const validateRequest = {
      programCode: `
        x := 5;
        y := 10;
        z := x + y;
        assert(z == 15);
      `
    };
    
    const validateResponse = await makeRequest('POST', '/api/parse/validate', validateRequest);
    console.log('Validate response:', validateResponse);
    
    return parseResponse.statusCode === 200 && 
           validateResponse.statusCode === 200 && 
           parseResponse.data.success && 
           validateResponse.data.valid;
  } catch (error) {
    console.log('Error testing parse endpoint:', error.message);
    return false;
  }
}

/**
 * Test invalid request handling
 */
async function testInvalidRequest() {
  console.log('\n=== Testing invalid requests handling ===');
  
  try {
    // Empty request to equivalence endpoint
    const emptyRequest = {};
    
    const emptyResponse = await makeRequest('POST', '/api/equivalence/check', emptyRequest);
    console.log('Empty request response:', emptyResponse);
    
    // Malformed request to verify endpoint
    const malformedRequest = {
      program: 'x = 5;' // Incorrect syntax
    };
    
    const malformedResponse = await makeRequest('POST', '/api/verify', malformedRequest);
    console.log('Malformed request response:', malformedResponse);
    
    if (emptyResponse.statusCode === 400 && emptyResponse.data.success === false) {
      console.log('Expected error received for invalid request');
      return true;
    } else {
      console.log('Invalid request handling failed');
      return false;
    }
  } catch (error) {
    console.log('Error testing invalid requests:', error.message);
    return false;
  }
}

/**
 * Run all API tests
 */
async function runTests() {
  console.log('Starting API tests...');
  
  const results = {
    verify: await testVerifyEndpoint(),
    equivalence: await testEquivalenceEndpoint(),
    parse: await testParseEndpoint(),
    invalidRequest: await testInvalidRequest()
  };
  
  console.log('\n=== Test Results Summary ===');
  for (const [test, passed] of Object.entries(results)) {
    console.log(`- ${test}: ${passed ? 'PASSED' : 'FAILED'}`);
  }
  
  const allPassed = Object.values(results).every(r => r);
  console.log(`\nOverall: ${allPassed ? 'ALL TESTS PASSED' : 'SOME TESTS FAILED'}`);
  console.log('Testing completed');
}

// Run the tests if this script is executed directly
if (require.main === module) {
  runTests().catch(err => {
    console.error('Error running tests:', err);
    process.exit(1);
  });
}

module.exports = { runTests };
