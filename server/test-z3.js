/**
 * Test script for Z3 solver integration
 * Tests real Z3 solver implementation without mocks
 */
const z3Service = require('./src/services/z3Service');

/**
 * Test for failing verification
 * This test ensures that sum > product fails when x=5, y=10
 */
async function testFailingVerification() {
  console.log("\n=== Testing failing verification (sum > product) ===");
  
  const constraints = {
    smtScript: `
      (declare-const x Int)
      (declare-const y Int)
      (declare-const sum Int)
      (declare-const product Int)
      
      ; Set up the scenario
      (assert (= x 5))
      (assert (= y 10))
      (assert (= sum (+ x y)))    ; sum = 15
      (assert (= product (* x y))) ; product = 50
      
      ; Negate the assertion to check for counterexample
      (assert (not (> sum product)))
    `,
    declarations: [
      'declare-const x Int',
      'declare-const y Int',
      'declare-const sum Int',
      'declare-const product Int'
    ],
    variables: ['x', 'y', 'sum', 'product']
  };
  
  try {
    const result = await z3Service.verifyAssertions(constraints);
    console.log("Verification result:", JSON.stringify(result, null, 2));
    
    if (result.success && !result.verified) {
      console.log("✓ Test passed: sum > product correctly fails verification");
      
      if (result.counterexample) {
        console.log("✓ Counterexample found correctly");
      } else {
        console.log("✗ No counterexample provided");
      }
    } else {
      console.log("✗ Test failed: Expected failure verification, got:", result);
    }
  } catch (error) {
    console.error("Error in test:", error);
  }
}

/**
 * Test for passing verification
 * This test ensures that sum < product passes when x=5, y=10
 */
async function testPassingVerification() {
  console.log("\n=== Testing passing verification (sum < product) ===");
  
  const constraints = {
    smtScript: `
      (declare-const x Int)
      (declare-const y Int)
      (declare-const sum Int)
      (declare-const product Int)
      
      ; Set up the scenario
      (assert (= x 5))
      (assert (= y 10))
      (assert (= sum (+ x y)))    ; sum = 15
      (assert (= product (* x y))) ; product = 50
      
      ; Negate the assertion to check for counterexample
      (assert (not (< sum product)))
    `,
    declarations: [
      'declare-const x Int',
      'declare-const y Int',
      'declare-const sum Int',
      'declare-const product Int'
    ],
    variables: ['x', 'y', 'sum', 'product']
  };
  
  try {
    const result = await z3Service.verifyAssertions(constraints);
    console.log("Verification result:", JSON.stringify(result, null, 2));
    
    if (result.success && result.verified) {
      console.log("✓ Test passed: sum < product correctly passes verification");
    } else {
      console.log("✗ Test failed: Expected successful verification, got:", result);
      
      if (result.counterexample) {
        console.log("Unexpected counterexample:", result.counterexample);
      }
    }
  } catch (error) {
    console.error("Error in test:", error);
  }
}

/**
 * Test for program equivalence
 * This test ensures that two equivalent programs are correctly identified
 */
async function testEquivalence() {
  console.log("\n=== Testing program equivalence ===");
  
  const constraints = {
    smtScript: `
      (declare-const x Int)
      (declare-const y Int)
      
      ; Program 1
      (declare-const result_1 Int)
      (assert (= result_1 (+ x y)))
      
      ; Program 2
      (declare-const result_2 Int)
      (assert (= result_2 (+ y x)))
      
      ; Check if they can be not equal (counterexample to equivalence)
      (assert (not (= result_1 result_2)))
    `,
    declarations: [
      'declare-const x Int',
      'declare-const y Int',
      'declare-const result_1 Int',
      'declare-const result_2 Int'
    ],
    variables: ['x', 'y', 'result_1', 'result_2']
  };
  
  try {
    const result = await z3Service.checkEquivalence(constraints);
    console.log("Equivalence result:", JSON.stringify(result, null, 2));
    
    if (result.success && result.equivalent) {
      console.log("✓ Test passed: Programs correctly identified as equivalent");
    } else {
      console.log("✗ Test failed: Programs should be equivalent, got:", result);
      
      if (result.counterexample) {
        console.log("Unexpected counterexample:", result.counterexample);
      }
    }
  } catch (error) {
    console.error("Error in test:", error);
  }
}

/**
 * Test for program non-equivalence
 * This test ensures that two non-equivalent programs are correctly identified
 */
async function testNonEquivalence() {
  console.log("\n=== Testing program non-equivalence ===");
  
  const constraints = {
    smtScript: `
      (declare-const x Int)
      (declare-const y Int)
      
      ; Program 1
      (declare-const result_1 Int)
      (assert (= result_1 (+ x y)))
      
      ; Program 2
      (declare-const result_2 Int)
      (assert (= result_2 (* x y)))
      
      ; Check if they can be not equal (counterexample to equivalence)
      (assert (not (= result_1 result_2)))
    `,
    declarations: [
      'declare-const x Int',
      'declare-const y Int',
      'declare-const result_1 Int',
      'declare-const result_2 Int'
    ],
    variables: ['x', 'y', 'result_1', 'result_2']
  };
  
  try {
    const result = await z3Service.checkEquivalence(constraints);
    console.log("Non-equivalence result:", JSON.stringify(result, null, 2));
    
    if (result.success && !result.equivalent) {
      console.log("✓ Test passed: Programs correctly identified as non-equivalent");
      
      if (result.counterexample) {
        console.log("✓ Counterexample showing the difference found correctly");
      } else {
        console.log("✗ No counterexample provided");
      }
    } else {
      console.log("✗ Test failed: Programs should not be equivalent, got:", result);
    }
  } catch (error) {
    console.error("Error in test:", error);
  }
}

/**
 * Run all tests
 */
async function runTests() {
  console.log("=== Z3 Service Real Implementation Tests ===");
  
  try {
    // Initialize Z3
    await z3Service.initialize();
    console.log("Z3 initialized successfully");
    
    // Run individual tests
    await testFailingVerification();
    await testPassingVerification();
    await testEquivalence();
    await testNonEquivalence();
    
    console.log("\n=== All tests completed ===");
  } catch (error) {
    console.error("Fatal error running tests:", error);
  }
}

// Run the tests
runTests().catch(console.error); 