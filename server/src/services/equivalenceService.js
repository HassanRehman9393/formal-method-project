/**
 * Equivalence Service
 * Provides functionality for checking program equivalence
 */
const parserService = require('./parserService');
const ssaService = require('./ssaService');
const smtGenerationService = require('./smtGenerationService');
const z3Service = require('./z3Service');

class EquivalenceService {
  constructor() {
    console.log('[EquivalenceService] Service initialized');
  }

  /**
   * Check if two programs are semantically equivalent
   * 
   * @param {String} program1 - First program to compare
   * @param {String} program2 - Second program to compare
   * @param {Object} options - Comparison options
   * @returns {Object} - Equivalence check results
   */
  async checkEquivalence(program1, program2, options = {}) {
    console.log('[EquivalenceService] Checking equivalence between programs');
    
    try {
      // Parse both programs
      const ast1 = await parserService.parseProgram(program1);
      const ast2 = await parserService.parseProgram(program2);
      
      if (!ast1.success || !ast2.success) {
        return {
          success: false,
          message: ast1.success ? 
            `Error parsing second program: ${ast2.error}` : 
            `Error parsing first program: ${ast1.error}`
        };
      }
      
      // Transform to SSA if required
      const loopUnrollDepth = options.loopUnrollDepth || 5;
      let ssaAst1, ssaAst2;
      
      if (options.useSSA !== false) {
        ssaAst1 = await ssaService.transformToSSA(ast1.ast, { loopUnrollDepth });
        ssaAst2 = await ssaService.transformToSSA(ast2.ast, { loopUnrollDepth });
        
        if (!ssaAst1.success || !ssaAst2.success) {
          return {
            success: false,
            message: ssaAst1.success ? 
              `Error transforming second program to SSA: ${ssaAst2.error}` : 
              `Error transforming first program to SSA: ${ssaAst1.error}`
          };
        }
      }
      
      // Generate SMT constraints for equivalence checking
      const constraints = await smtGenerationService.generateConstraintsForEquivalence(
        ssaAst1?.ssaAst || ast1.ast,
        ssaAst2?.ssaAst || ast2.ast,
        options
      );
      
      if (!constraints.success) {
        return {
          success: false,
          message: `Error generating equivalence constraints: ${constraints.error}`
        };
      }
      
      // Verify using Z3 service
      const result = await z3Service.checkEquivalence(constraints, options);
      
      // A satisfiable result means the programs are not equivalent
      // (we negate the equivalence condition in the SMT constraints)
      const isEquivalent = result.equivalent;
      
      return {
        success: true,
        data: {
          equivalent: isEquivalent,
          message: result.message || (isEquivalent ? 
            'The programs are semantically equivalent' : 
            'The programs are not equivalent'),
          counterexample: isEquivalent ? null : result.counterexample,
          time: result.executionTime || 0,
          timedOut: result.timedOut || false
        }
      };
    } catch (error) {
      console.error('[EquivalenceService] Error checking equivalence:', error);
      return {
        success: false,
        message: `Error checking equivalence: ${error.message}`
      };
    }
  }

  /**
   * Generate a detailed report of equivalence check
   * 
   * @param {Object} result - Equivalence check result
   * @param {String} format - Report format (json, html, text)
   * @returns {String} - Formatted report
   */
  generateEquivalenceReport(result, format = 'json') {
    console.log('[EquivalenceService] Generating equivalence report in format:', format);
    
    if (format === 'html') {
      return `
        <html>
          <head><title>Equivalence Report</title></head>
          <body>
            <h1>Program Equivalence Report</h1>
            <p><strong>Equivalent:</strong> ${result.data.equivalent ? 'Yes' : 'No'}</p>
            ${!result.data.equivalent && result.data.counterexample ? `
              <h2>Counterexample</h2>
              <pre>${JSON.stringify(result.data.counterexample, null, 2)}</pre>
              ${result.data.counterexample.trace ? `
                <h3>Execution Trace</h3>
                <pre>${JSON.stringify(result.data.counterexample.trace, null, 2)}</pre>
              ` : ''}
            ` : ''}
            <p><strong>Execution Time:</strong> ${result.data.time || 0}ms</p>
          </body>
        </html>
      `;
    } else if (format === 'text') {
      return `
Program Equivalence Report
==========================
Equivalent: ${result.data.equivalent ? 'Yes' : 'No'}
${!result.data.equivalent && result.data.counterexample ? `
Counterexample:
${JSON.stringify(result.data.counterexample, null, 2)}
${result.data.counterexample.trace ? `
Execution Trace:
${JSON.stringify(result.data.counterexample.trace, null, 2)}
` : ''}
` : ''}
Execution Time: ${result.data.time || 0}ms
      `;
    } else {
      // JSON format
      return JSON.stringify(result, null, 2);
    }
  }
}

// Export the class instead of a singleton instance
module.exports = EquivalenceService;
