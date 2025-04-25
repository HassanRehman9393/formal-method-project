/**
 * Verification Controller
 * Handles API requests related to program verification
 */
const verificationService = require('../services/verificationService');
const parserService = require('../services/parserService');

/**
 * Verify a program's assertions and postconditions
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.verifyProgram = async (req, res) => {
  try {
    const { program, ast, options, postconditions } = req.body;
    
    if (!program && !ast) {
      return res.status(400).json({
        success: false,
        error: 'Either program code or AST is required'
      });
    }
    
    // Extract verification options
    const verificationOptions = {
      loopUnrollDepth: options?.loopUnrollDepth || 5,
      includeArrays: options?.includeArrays !== false,
      ...options
    };
    
    // Parse the program if AST is not provided
    let programAst = ast;
    if (!programAst && program) {
      try {
        // This assumes parserService exists and has a parse method
        // If not implemented yet, return an error
        programAst = { type: 'Program', body: [] };
        // programAst = await parserService.parse(program);
      } catch (parseError) {
        return res.status(400).json({
          success: false,
          error: `Parser error: ${parseError.message}`
        });
      }
    }
    
    // Verify the program
    let result;
    if (postconditions) {
      result = await verificationService.verifyPostconditions(
        programAst,
        postconditions,
        verificationOptions
      );
    } else {
      result = await verificationService.verifyAssertions(
        programAst,
        verificationOptions
      );
    }
    
    // Check if verification was successful
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error || 'Verification failed'
      });
    }
    
    // Return the verification results
    return res.status(200).json({
      success: true,
      verified: result.verified,
      status: result.status,
      message: result.message,
      counterexamples: result.counterexamples || [],
      time: result.time
    });
  } catch (error) {
    console.error('Error during verification:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during verification',
      message: error.message
    });
  }
};

/**
 * Verify a program from SSA form
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.verifyFromSSA = async (req, res) => {
  try {
    const { ssaProgram, options } = req.body;
    
    if (!ssaProgram) {
      return res.status(400).json({
        success: false,
        error: 'SSA program is required'
      });
    }
    
    // Extract verification options
    const verificationOptions = {
      ...options
    };
    
    // Verify from SSA
    const result = await verificationService.verifyFromSSA(ssaProgram, verificationOptions);
    
    // Check if verification was successful
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error || 'Verification from SSA failed'
      });
    }
    
    // Return the verification results
    return res.status(200).json({
      success: true,
      verified: result.verified,
      status: result.status,
      message: result.message,
      counterexamples: result.counterexamples || [],
      time: result.time
    });
  } catch (error) {
    console.error('Error during verification from SSA:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during verification',
      message: error.message
    });
  }
};

/**
 * Generate verification report in different formats
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.generateReport = async (req, res) => {
  try {
    const { result, format } = req.body;
    
    if (!result) {
      return res.status(400).json({
        success: false,
        error: 'Verification result is required'
      });
    }
    
    // Generate report in specified format
    const report = verificationService.generateReport(result, format);
    
    // Set appropriate response content type
    if (format === 'html') {
      res.setHeader('Content-Type', 'text/html');
    } else if (format === 'text') {
      res.setHeader('Content-Type', 'text/plain');
    } else {
      res.setHeader('Content-Type', 'application/json');
    }
    
    return res.status(200).send(report);
  } catch (error) {
    console.error('Error generating verification report:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error generating report',
      message: error.message
    });
  }
};

/**
 * Check equivalence between two programs
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.checkEquivalence = async (req, res) => {
  try {
    const { program1, program2, ast1, ast2, options, outputs } = req.body;
    
    // Ensure we have at least one method to get both programs
    if ((!program1 && !ast1) || (!program2 && !ast2)) {
      return res.status(400).json({
        success: false,
        error: 'Both programs are required (either as code or AST)'
      });
    }
    
    // Define verification options
    const verificationOptions = {
      loopUnrollDepth: options?.loopUnrollDepth || 5,
      ...options
    };
    
    // Parse programs if ASTs are not provided
    let programAst1 = ast1;
    let programAst2 = ast2;
    
    if (!programAst1 && program1) {
      try {
        // This is a placeholder. In reality, you would use your parser service
        programAst1 = { type: 'Program', body: [] };
        // programAst1 = await parserService.parse(program1);
      } catch (parseError) {
        return res.status(400).json({
          success: false,
          error: `Parser error in program 1: ${parseError.message}`
        });
      }
    }
    
    if (!programAst2 && program2) {
      try {
        // This is a placeholder
        programAst2 = { type: 'Program', body: [] };
        // programAst2 = await parserService.parse(program2);
      } catch (parseError) {
        return res.status(400).json({
          success: false,
          error: `Parser error in program 2: ${parseError.message}`
        });
      }
    }
    
    // If outputs are not specified, try to infer them from the ASTs
    let outputVars = outputs;
    if (!outputVars || outputVars.length === 0) {
      // This would be the implementation for auto-detecting outputs
      outputVars = ['result']; // Default placeholder
    }
    
    // Check equivalence
    const result = await verificationService.checkEquivalence(
      programAst1,
      programAst2,
      outputVars,
      verificationOptions
    );
    
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error || 'Equivalence checking failed'
      });
    }
    
    return res.status(200).json({
      success: true,
      equivalent: result.equivalent,
      status: result.equivalent ? 'Programs are equivalent' : 'Programs are not equivalent',
      message: result.message,
      counterexample: result.counterexample || null,
      time: result.time
    });
  } catch (error) {
    console.error('Error checking equivalence:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during equivalence checking',
      message: error.message
    });
  }
};
