// CommonJS style import
const fetch = (...args) => import('node-fetch').then(({default: fetch}) => fetch(...args));

// API base URL
const API_BASE_URL = 'http://localhost:3001/api';

// Test program 1
const program1 = `
x := 5;
y := 10;
sum := x + y;
assert(sum > 0);
`;

// Test program 2
const program2 = `
a := 5;
b := 10;
result := a + b;
`;

// Test functions
async function testParse() {
  console.log('Testing /parse endpoint...');
  
  try {
    const response = await fetch(`${API_BASE_URL}/parse`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ programCode: program1 })
    });
    
    const data = await response.json();
    console.log('Parse result:', JSON.stringify(data, null, 2));
    return data;
  } catch (error) {
    console.error('Error testing parse:', error);
  }
}

async function testSSATransform(ast) {
  console.log('Testing /parse/transform-ssa endpoint...');
  
  try {
    const response = await fetch(`${API_BASE_URL}/parse/transform-ssa`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ 
        ast: ast || null,
        programCode: !ast ? program1 : null,
        loopUnrollingDepth: 5 
      })
    });
    
    const data = await response.json();
    console.log('SSA transform result:', JSON.stringify(data, null, 2));
    return data;
  } catch (error) {
    console.error('Error testing SSA transform:', error);
  }
}

async function testGenerateSMT() {
  console.log('Testing /verify/generate-smt endpoint...');
  
  try {
    const response = await fetch(`${API_BASE_URL}/verify/generate-smt`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ 
        program: program1,
        options: { loopUnrollDepth: 5 } 
      })
    });
    
    const data = await response.json();
    console.log('Generate SMT result:', JSON.stringify(data, null, 2));
    return data;
  } catch (error) {
    console.error('Error testing Generate SMT:', error);
  }
}

async function testVerify() {
  console.log('Testing /verify endpoint...');
  
  try {
    const response = await fetch(`${API_BASE_URL}/verify`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ 
        program: program1,
        options: { loopUnrollDepth: 5 } 
      })
    });
    
    const data = await response.json();
    console.log('Verify result:', JSON.stringify(data, null, 2));
    return data;
  } catch (error) {
    console.error('Error testing Verify:', error);
  }
}

async function testEquivalence() {
  console.log('Testing /equivalence endpoint...');
  
  try {
    const response = await fetch(`${API_BASE_URL}/equivalence`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ 
        program1: program1,
        program2: program2,
        options: { loopUnrollDepth: 5 } 
      })
    });
    
    const data = await response.json();
    console.log('Equivalence result:', JSON.stringify(data, null, 2));
    return data;
  } catch (error) {
    console.error('Error testing Equivalence:', error);
  }
}

// Run all tests
async function runTests() {
  console.log('Starting API tests...');
  
  // Test parse endpoint
  const parseResult = await testParse();
  
  // Test SSA transform endpoint
  const ssaResult = await testSSATransform(parseResult?.ast);
  
  // Test generate SMT endpoint
  await testGenerateSMT();
  
  // Test verify endpoint
  await testVerify();
  
  // Test equivalence endpoint
  await testEquivalence();
  
  console.log('All tests completed.');
}

// Run the tests
runTests(); 