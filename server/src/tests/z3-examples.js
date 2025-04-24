/**
 * Z3 Test Examples
 * This file contains examples to test the Z3 solver integration
 */
const z3Service = require('../services/z3Service');

/**
 * Run all tests
 */
async function runAllTests() {
  console.log('Running Z3 integration tests...');
  
  try {
    // Test 1: Simple constraint problem
    console.log('\n--- Test 1: Simple Constraint Problem ---');
    const simpleResult = await z3Service.runTest();
    console.log('Simple test result:', simpleResult);
    
    // Test 2: Manual Z3 API usage
    console.log('\n--- Test 2: Manual Z3 API Usage ---');
    await testManualZ3Api();
    
    // Test 3: System of linear equations
    console.log('\n--- Test 3: System of Linear Equations ---');
    await testLinearEquations();
    
    console.log('\nAll Z3 tests completed.');
  } catch (error) {
    console.error('Error running tests:', error);
  }
}

/**
 * Test manual Z3 API usage
 */
async function testManualZ3Api() {
  try {
    await z3Service.initialize();
    const { z3, solver } = await z3Service.getContext();
    
    console.log('Creating boolean variables...');
    // Create boolean variables
    const p = z3.Bool.const('p');
    const q = z3.Bool.const('q');
    const r = z3.Bool.const('r');
    
    console.log('Adding constraints...');
    // p implies q
    solver.add(z3.Implies(p, q));
    // q implies r
    solver.add(z3.Implies(q, r));
    // not r
    solver.add(z3.Not(r));
    
    // Check if p is false (should be unsat if p is true)
    console.log('Pushing solver state...');
    solver.push();
    solver.add(p);
    
    console.log('Checking if p is true...');
    const result = await solver.check();
    console.log(`Is p true? ${result}`);
    
    if (result === 'sat') {
      const model = solver.model();
      console.log('Model:', {
        p: model.eval(p).toString(),
        q: model.eval(q).toString(),
        r: model.eval(r).toString()
      });
    }
    
    console.log('Popping solver state...');
    solver.pop();
    
    // Check if not p is true (should be sat)
    console.log('Pushing solver state...');
    solver.push();
    solver.add(z3.Not(p));
    
    console.log('Checking if not p is true...');
    const result2 = await solver.check();
    console.log(`Is not p true? ${result2}`);
    
    if (result2 === 'sat') {
      const model = solver.model();
      console.log('Model:', {
        p: model.eval(p).toString(),
        q: model.eval(q).toString(),
        r: model.eval(r).toString()
      });
    }
    
    console.log('Popping solver state...');
    solver.pop();
    
  } catch (error) {
    console.error('Error in manual Z3 API test:', error);
  }
}

/**
 * Test system of linear equations
 */
async function testLinearEquations() {
  try {
    await z3Service.initialize();
    const { z3, solver } = await z3Service.getContext();
    
    console.log('Creating integer variables...');
    // Create integer variables
    const x = z3.Int.const('x');
    const y = z3.Int.const('y');
    const z = z3.Int.const('z');
    
    console.log('Adding equations...');
    
    // Create integer constants
    const zero = z3.Int.val(0);
    const one = z3.Int.val(1);
    const two = z3.Int.val(2);
    const three = z3.Int.val(3);
    const five = z3.Int.val(5);
    const negOne = z3.Int.val(-1);
    const negTwo = z3.Int.val(-2);
    const negFive = z3.Int.val(-5);
    
    // 2x + y - z = 1
    // Create an expression by adding the terms without using Mul
    const eq1_left = z3.Add([x, x, y]); // 2x + y
    const eq1 = z3.Eq(z3.Sub(eq1_left, z), one); // (2x + y) - z = 1
    solver.add(eq1);
    
    // 3x - 5y = -2
    // For 3x, add x three times
    const term1 = z3.Add([x, x, x]); // 3x
    // For -5y, negate y 5 times and add them
    const term2 = z3.Mul(negFive, y); // Trying with negFive * y
    const eq2 = z3.Eq(z3.Add([term1, term2]), negTwo); // 3x + (-5y) = -2
    solver.add(eq2);
    
    // x + y + z = 5
    solver.add(z3.Eq(z3.Add([x, y, z]), five));
    
    console.log('Checking satisfiability...');
    const result = await solver.check();
    console.log(`Is the system satisfiable? ${result}`);
    
    if (result === 'sat') {
      const model = solver.model();
      console.log('Solution:', {
        x: model.eval(x).toString(),
        y: model.eval(y).toString(),
        z: model.eval(z).toString()
      });
      
      // Verify solution
      const solution = {
        x: parseInt(model.eval(x).toString()),
        y: parseInt(model.eval(y).toString()),
        z: parseInt(model.eval(z).toString())
      };
      
      console.log('Verification:');
      console.log(`2*${solution.x} + ${solution.y} - ${solution.z} = ${2*solution.x + solution.y - solution.z}`);
      console.log(`3*${solution.x} - 5*${solution.y} = ${3*solution.x - 5*solution.y}`);
      console.log(`${solution.x} + ${solution.y} + ${solution.z} = ${solution.x + solution.y + solution.z}`);
    }
    
  } catch (error) {
    console.error('Error in linear equations test:', error);
  }
}

// Run the tests if this module is executed directly
if (require.main === module) {
  runAllTests();
}

module.exports = { runAllTests };
