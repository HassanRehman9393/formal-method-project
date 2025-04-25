/**
 * Sample programs for testing equivalence checking
 */
module.exports = {
  /**
   * Basic equivalent programs - different implementations of sum
   */
  basicEquivalent: {
    program1: {
      code: `
        // Program 1: Sum using intermediate variable
        x := 5;
        y := 10;
        temp := x + y;
        result := temp;
      `
    },
    program2: {
      code: `
        // Program 2: Direct sum
        x := 5;
        y := 10;
        result := x + y;
      `
    },
    options: {
      outputs: ['result']
    },
    expectedResult: true
  },
  
  /**
   * Basic inequivalent programs - sum vs multiply
   */
  basicInequivalent: {
    program1: {
      code: `
        // Program 1: Sum
        x := 5;
        y := 10;
        result := x + y;
      `
    },
    program2: {
      code: `
        // Program 2: Multiply
        x := 5;
        y := 10;
        result := x * y;
      `
    },
    options: {
      outputs: ['result']
    },
    expectedResult: false
  },
  
  /**
   * Equivalent programs with conditionals
   */
  conditionalEquivalent: {
    program1: {
      code: `
        // Program 1: Using if-else
        x := input;
        
        if (x > 0) {
          result := x * 2;
        } else {
          result := x * -1;
        }
      `
    },
    program2: {
      code: `
        // Program 2: Using ternary expression
        x := input;
        result := x > 0 ? x * 2 : x * -1;
      `
    },
    options: {
      outputs: ['result']
    },
    expectedResult: true
  },
  
  /**
   * Equivalent programs with arrays
   */
  arrayEquivalent: {
    program1: {
      code: `
        // Program 1: Using direct assignments
        arr[0] := 1;
        arr[1] := 2;
        arr[2] := 3;
      `
    },
    program2: {
      code: `
        // Program 2: Using a loop
        i := 0;
        while (i < 3) {
          arr[i] := i + 1;
          i := i + 1;
        }
      `
    },
    options: {
      outputs: ['arr'],
      arrayOutputs: ['arr'],
      loopUnrollDepth: 3
    },
    expectedResult: true
  },
  
  /**
   * Subtle inequivalent programs - off-by-one error
   */
  subtleInequivalent: {
    program1: {
      code: `
        // Program 1: Sum from 1 to n
        n := input;
        sum := 0;
        i := 1;
        
        while (i <= n) {
          sum := sum + i;
          i := i + 1;
        }
        
        result := sum;
      `
    },
    program2: {
      code: `
        // Program 2: Off-by-one error
        n := input;
        sum := 0;
        i := 1;
        
        while (i < n) { // Note the < instead of <=
          sum := sum + i;
          i := i + 1;
        }
        
        result := sum;
      `
    },
    options: {
      outputs: ['result'],
      loopUnrollDepth: 5
    },
    expectedResult: false
  },
  
  /**
   * Complex equivalent programs - different algorithms for same computation
   */
  complexEquivalent: {
    program1: {
      code: `
        // Program 1: Fibonacci using iteration
        n := input;
        a := 0;
        b := 1;
        i := 0;
        
        while (i < n) {
          temp := a;
          a := b;
          b := temp + b;
          i := i + 1;
        }
        
        result := a;
      `
    },
    program2: {
      code: `
        // Program 2: Fibonacci using direct formula
        // Using the closed-form expression for small values
        n := input;
        
        if (n == 0) {
          result := 0;
        } else if (n == 1) {
          result := 1;
        } else if (n == 2) {
          result := 1;
        } else if (n == 3) {
          result := 2;
        } else if (n == 4) {
          result := 3;
        } else if (n == 5) {
          result := 5;
        } else if (n == 6) {
          result := 8;
        } else {
          result := 0; // Beyond our testing range
        }
      `
    },
    options: {
      outputs: ['result'],
      loopUnrollDepth: 6
    },
    expectedResult: true
  }
};
