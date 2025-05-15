/**
 * Verification Service
 * Handles program verification logic
 */
const z3Service = require('./z3Service');
const smtGenerationService = require('./smtGenerationService');
const ssaService = require('./ssaService');
const parserService = require('./parserService');

class VerificationService {
  constructor() {
    console.log('[VerificationService] Service initialized');
  }

  /**
   * Verify a program's assertions
   * 
   * @param {Object} ast - Program AST
   * @param {Object} options - Verification options
   * @returns {Object} - Verification results
   */
  async verifyAssertions(ast, options = {}) {
    console.log('[VerificationService] Verifying assertions');
    
    try {
      // Generate SMT constraints from the AST
      const constraints = await smtGenerationService.generateConstraints(ast, options);
      
      if (!constraints.success) {
        return {
          success: false,
          error: constraints.error || 'Failed to generate constraints'
        };
      }
      
      // Verify the constraints using Z3
      const result = await z3Service.verifyAssertions(constraints, options);
    
      return {
        success: true,
        verified: result.verified,
        message: result.message,
        counterexamples: result.counterexample ? [result.counterexample] : [],
        time: result.executionTime || 0,
        timedOut: result.timedOut || false
      };
    } catch (error) {
      console.error('[VerificationService] Error verifying assertions:', error);
      return {
        success: false,
        error: error.message
    };
    }
  }

  /**
   * Verify a program's postconditions
   * 
   * @param {Object} ast - Program AST
   * @param {Array} postconditions - List of postconditions
   * @param {Object} options - Verification options
   * @returns {Object} - Verification results
   */
  async verifyPostconditions(ast, postconditions, options = {}) {
    console.log('[VerificationService] Verifying postconditions');
    
    try {
      // Generate SMT constraints from the AST and postconditions
      const constraints = await smtGenerationService.generateConstraints(ast, options);
      
      if (!constraints.success) {
        return {
          success: false,
          error: constraints.error || 'Failed to generate constraints'
        };
      }
      
      // Add postconditions to the constraints
      constraints.assertions = [
        ...constraints.assertions,
        ...postconditions.map(postcondition => ({
          constraint: postcondition,
          description: 'Postcondition'
        }))
      ];
      
      // Verify the constraints using Z3
      const result = await z3Service.verifyAssertions(constraints, options);
    
      return {
        success: true,
        verified: result.verified,
        message: result.message,
        counterexamples: result.counterexample ? [result.counterexample] : [],
        time: result.executionTime || 0,
        timedOut: result.timedOut || false
      };
    } catch (error) {
      console.error('[VerificationService] Error verifying postconditions:', error);
      return {
        success: false,
        error: error.message
    };
    }
  }

  /**
   * Verify a program from its SSA form
   * 
   * @param {Object} ssaProgram - Program in SSA form
   * @param {Object} options - Verification options
   * @returns {Object} - Verification results
   */
  async verifyFromSSA(ssaProgram, options = {}) {
    console.log('[VerificationService] Verifying from SSA');
    
    try {
      // Generate SMT constraints from the SSA program
      const constraints = await smtGenerationService.generateConstraints(ssaProgram, options);
      
      if (!constraints.success) {
        return {
          success: false,
          error: constraints.error || 'Failed to generate constraints from SSA'
        };
      }
      
      // Verify the constraints using Z3
      const result = await z3Service.verifyAssertions(constraints, options);
      
      return {
        success: true,
        verified: result.verified,
        message: result.message,
        counterexamples: result.counterexample ? [result.counterexample] : [],
        time: result.executionTime || 0,
        timedOut: result.timedOut || false
      };
    } catch (error) {
      console.error('[VerificationService] Error verifying from SSA:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Verify if two programs are semantically equivalent
   * 
   * @param {string} program1 - First program code
   * @param {string} program2 - Second program code
   * @param {Object} options - Verification options
   * @returns {Object} - Verification results
   */
  async checkEquivalence(program1, program2, options = {}) {
    console.log('[VerificationService] Checking program equivalence');
    
    try {
      // Parse programs
      const parseResult1 = await parserService.parseProgram(program1);
      const parseResult2 = await parserService.parseProgram(program2);
      
      if (!parseResult1.success || !parseResult2.success) {
        return {
          success: false,
          error: !parseResult1.success ? parseResult1.error : parseResult2.error
        };
      }
      
      // Transform to SSA
      const ssaResult1 = await ssaService.transformToSSA(parseResult1.ast, options);
      const ssaResult2 = await ssaService.transformToSSA(parseResult2.ast, options);
      
      if (!ssaResult1.success || !ssaResult2.success) {
        return {
          success: false,
          error: !ssaResult1.success ? ssaResult1.error : ssaResult2.error
        };
      }
      
      // Generate combined constraints for equivalence checking
      const constraints = await smtGenerationService.generateConstraintsForEquivalence(
        ssaResult1.ssaAst,
        ssaResult2.ssaAst,
        options
      );
      
      if (!constraints.success) {
        return {
          success: false,
          error: constraints.error || 'Failed to generate equivalence constraints'
        };
      }
      
      // Check equivalence using Z3
      const result = await z3Service.checkEquivalence(constraints, options);
      
      // Format counterexample for frontend if available
      if (!result.equivalent && result.counterexample) {
        result.counterexample = this.formatCounterexampleForFrontend(result.counterexample);
      }
      
      return {
        success: true,
        equivalent: result.equivalent,
        message: result.message,
        counterexample: result.counterexample,
        time: result.executionTime || 0
      };
    } catch (error) {
      console.error('[VerificationService] Error checking program equivalence:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Generate a verification report
   * 
   * @param {Object} result - Verification result
   * @param {String} format - Report format (json, html, text)
   * @returns {String} - Report in specified format
   */
  generateReport(result, format = 'json') {
    console.log('[VerificationService] Generating report', format);
    
    if (format === 'html') {
      return `
        <html>
          <head><title>Verification Report</title></head>
          <body>
            <h1>Verification Report</h1>
            <p><strong>Verified:</strong> ${result.verified ? 'Yes' : 'No'}</p>
            ${!result.verified && result.counterexamples && result.counterexamples.length > 0 ? `
              <h2>Counterexamples</h2>
              <pre>${JSON.stringify(result.counterexamples, null, 2)}</pre>
            ` : ''}
            <p><strong>Execution Time:</strong> ${result.time || 0}ms</p>
          </body>
        </html>
      `;
    } else if (format === 'text') {
      return `
Verification Report
===================
Verified: ${result.verified ? 'Yes' : 'No'}
${!result.verified && result.counterexamples && result.counterexamples.length > 0 ? `
Counterexamples:
${JSON.stringify(result.counterexamples, null, 2)}
` : ''}
Execution Time: ${result.time || 0}ms
      `;
    } else {
      return JSON.stringify({
        verified: result.verified,
        counterexamples: result.counterexamples || [],
        executionTime: result.time || 0,
        timedOut: result.timedOut || false
      }, null, 2);
    }
  }

  /**
   * Format counterexample results for the frontend
   * 
   * @param {Object} counterexample - Raw counterexample data from Z3 service
   * @returns {Object} - Formatted counterexample for frontend display
   */
  formatCounterexampleForFrontend(counterexample) {
    if (!counterexample) return null;
    
    // Initialize the formatted counterexample
    const formattedCounterexample = {
      variables: {},
      trace: []
    };
    
    // Extract inputs from counterexample
    if (counterexample.inputs) {
      formattedCounterexample.inputs = counterexample.inputs;
      
      // Also add to variables for backward compatibility
      formattedCounterexample.variables = { ...counterexample.inputs };
    }
    
    // Extract failed assertion if available
    if (counterexample.failedAssertion) {
      formattedCounterexample.failedAssertion = counterexample.failedAssertion;
    }
    
    // Extract execution trace if available
    if (counterexample.trace && Array.isArray(counterexample.trace)) {
      formattedCounterexample.trace = counterexample.trace.map(step => ({
        line: step.line || 0,
        statement: step.statement || '',
        state: step.state || {},
        branchTaken: step.branchTaken || null,
        conditionResult: step.conditionResult,
        assertionResult: step.assertionResult,
        variableChanged: step.variableChanged || null,
        arrayChanged: step.arrayChanged || null
      }));
    }
    
    // For array outputs in older format
    if (counterexample.outputs) {
      // Merge outputs into variables
      formattedCounterexample.variables = {
        ...formattedCounterexample.variables,
        ...counterexample.outputs
      };
    }
    
    return formattedCounterexample;
  }

  /**
   * Verify a program with assertions
   * 
   * @param {String} program - The program code to verify
   * @param {Object} options - Verification options
   * @returns {Promise<Object>} Verification result
   */
  async verifyProgram(program, options = {}) {
    try {
      console.log('[VerificationService] Verifying program with assertions');
      
      // Step 1: Parse the program
      const parseResult = await parserService.parseProgram(program);
      if (!parseResult.success) {
        return {
          success: false,
          error: parseResult.error,
          errorType: 'parser'
        };
      }
      
      // Step 2: Transform to SSA
      const ssaResult = await ssaService.transformToSSA(parseResult.ast, options);
      if (!ssaResult.success) {
        return {
          success: false,
          error: ssaResult.error,
          errorType: 'transformer'
        };
      }
      
      // Step 3: Generate SMT constraints
      const constraintsResult = await smtGenerationService.generateConstraints(ssaResult.ssaAst, options);
      if (!constraintsResult.success) {
        return {
          success: false,
          error: constraintsResult.error,
          errorType: 'smt'
        };
      }
      
      // Step 4: Optimize constraints if enabled
      const finalConstraints = options.skipOptimization 
        ? constraintsResult.constraints
        : this.constraintOptimizer.simplifyConstraints(constraintsResult.constraints);
      
      // Step 5: Verify assertions using the solver
      const verificationResult = await z3Service.verifyAssertions(finalConstraints, {
        timeout: options.timeout || 10000,
        loopUnrollingDepth: options.loopUnrollingDepth || 5
      });
      
      // Add SSA trace information to the counterexample if available
      if (!verificationResult.verified && verificationResult.counterexample) {
        // Generate trace from SSA and counterexample
        if (ssaResult.statements) {
          verificationResult.counterexample.trace = this.generateExecutionTrace(
            ssaResult.statements, 
            verificationResult.counterexample
          );
        }
        
        // Format counterexample for frontend
        verificationResult.counterexample = this.formatCounterexampleForFrontend(verificationResult.counterexample);
      }
      
      // Return verification result with counter-examples if assertions failed
      return {
        success: true,
        verified: verificationResult.verified,
        counterexamples: verificationResult.verified ? [] : [verificationResult.counterexample],
        message: verificationResult.message,
        timedOut: verificationResult.timedOut || false,
        executionTime: verificationResult.time
      };
    } catch (error) {
      console.error('[VerificationService] Error during verification:', error);
      return {
        success: false,
        error: `Verification error: ${error.message || error}`,
        errorType: 'solver'
      };
    }
  }
}

// Export a singleton instance
module.exports = new VerificationService();
