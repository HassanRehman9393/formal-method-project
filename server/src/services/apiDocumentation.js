/**
 * API Documentation for Formal Methods Program Analyzer
 */

const apiDocs = {
  // Verification endpoint
  verify: {
    endpoint: '/api/verify',
    method: 'POST',
    description: 'Verifies if all assertions in a program hold for all possible inputs',
    requestBody: {
      program: 'String - The program code to verify',
      loopUnrollingDepth: 'Number (optional) - Maximum loop unrolling depth (default: 3)'
    },
    responses: {
      200: {
        description: 'Successful verification',
        content: {
          success: 'Boolean - true',
          verified: 'Boolean - Whether assertions are verified',
          counterexample: 'Object (optional) - Example inputs that violate assertions',
          smtConstraints: 'String - Generated SMT constraints',
          ssaForm: 'String - Program in SSA form'
        }
      },
      400: {
        description: 'Invalid request',
        content: {
          success: 'Boolean - false',
          error: 'String - Error message'
        }
      },
      500: {
        description: 'Server error',
        content: {
          success: 'Boolean - false',
          error: 'String - Error message',
          message: 'String - Error details'
        }
      }
    }
  },

  // Equivalence endpoint
  equivalence: {
    endpoint: '/api/equivalence',
    method: 'POST',
    description: 'Checks if two programs are semantically equivalent',
    requestBody: {
      program1: 'String - First program code',
      program2: 'String - Second program code',
      loopUnrollingDepth: 'Number (optional) - Maximum loop unrolling depth (default: 3)'
    },
    responses: {
      200: {
        description: 'Successful equivalence check',
        content: {
          success: 'Boolean - true',
          equivalent: 'Boolean - Whether programs are equivalent',
          counterexample: 'Object (optional) - Example inputs that show inequivalence',
          smtConstraints: 'String - Generated SMT constraints'
        }
      },
      400: {
        description: 'Invalid request',
        content: {
          success: 'Boolean - false',
          error: 'String - Error message'
        }
      },
      500: {
        description: 'Server error',
        content: {
          success: 'Boolean - false',
          error: 'String - Error message',
          message: 'String - Error details'
        }
      }
    }
  },

  // Parse endpoint
  parse: {
    endpoint: '/api/parse',
    method: 'POST',
    description: 'Parses program and returns AST',
    requestBody: {
      program: 'String - The program code to parse'
    },
    responses: {
      200: {
        description: 'Successful parsing',
        content: {
          success: 'Boolean - true',
          ast: 'Object - Abstract Syntax Tree of the program'
        }
      },
      400: {
        description: 'Invalid request',
        content: {
          success: 'Boolean - false',
          error: 'String - Error message'
        }
      },
      500: {
        description: 'Server error',
        content: {
          success: 'Boolean - false',
          error: 'String - Error message',
          message: 'String - Error details'
        }
      }
    }
  }
};

module.exports = apiDocs;
