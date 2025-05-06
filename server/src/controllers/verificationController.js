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
      useIncrementalSolving: options?.useIncrementalSolving !== false,
      optimizeConstraints: options?.optimizeConstraints !== false,
      optimizeArrays: options?.optimizeArrays !== false,
      timeout: options?.timeout || 10000,
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
      timedOut: result.timedOut || false,
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

/**
 * Generate enhanced counterexamples with execution traces
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.generateEnhancedCounterexamples = async (req, res) => {
  try {
    const { program, ast, options, smtConstraints } = req.body;
    
    // Ensure we have either program code, AST, or direct SMT constraints
    if (!program && !ast && !smtConstraints) {
      return res.status(400).json({
        success: false,
        error: 'Either program code, AST, or SMT constraints are required'
      });
    }
    
    // Extract options for counterexample generation
    const counterexampleOptions = {
      maxCounterexamples: options?.maxCounterexamples || 3,
      includeTrace: options?.includeTrace !== false,
      loopUnrollDepth: options?.loopUnrollDepth || 5,
      ...options
    };
    
    // Generate enhanced counterexamples
    const result = await verificationService.generateEnhancedCounterexamples(
      program,
      ast,
      smtConstraints,
      counterexampleOptions
    );
    
    // Check if the operation was successful
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error || 'Failed to generate enhanced counterexamples'
      });
    }
    
    // Return the enhanced counterexamples
    return res.status(200).json({
      success: true,
      verified: result.verified,
      status: result.status,
      message: result.message,
      counterexamples: result.counterexamples || [],
      multipleCounterexamples: result.multipleCounterexamples || [],
      enhancedAnalysis: result.enhancedAnalysis || {},
      time: result.time
    });
  } catch (error) {
    console.error('Error generating enhanced counterexamples:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during counterexample generation',
      message: error.message
    });
  }
};

/**
 * Generate execution trace for a specific counterexample
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.generateExecutionTrace = async (req, res) => {
  try {
    const { program, counterexample, options } = req.body;
    
    if (!program) {
      return res.status(400).json({
        success: false,
        error: 'Program code is required'
      });
    }
    
    if (!counterexample) {
      return res.status(400).json({
        success: false,
        error: 'Counterexample is required'
      });
    }
    
    // Generate execution trace
    const result = await verificationService.generateTraceForCounterexample(
      program,
      counterexample,
      options
    );
    
    // Check if operation was successful
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error || 'Failed to generate execution trace'
      });
    }
    
    // Return the trace
    return res.status(200).json({
      success: true,
      trace: result.trace,
      violatingStep: result.violatingStep,
      time: result.time
    });
  } catch (error) {
    console.error('Error generating execution trace:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during trace generation',
      message: error.message
    });
  }
};

/**
 * Analyze multiple counterexamples to detect patterns
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.analyzeCounterexamples = async (req, res) => {
  try {
    const { counterexamples, program } = req.body;
    
    if (!counterexamples || !Array.isArray(counterexamples) || counterexamples.length === 0) {
      return res.status(400).json({
        success: false,
        error: 'At least one counterexample is required for analysis'
      });
    }
    
    // Perform analysis
    const result = await verificationService.analyzeCounterexamples(counterexamples, program);
    
    // Return the analysis
    return res.status(200).json({
      success: true,
      analysis: result.analysis,
      suggestedFixes: result.suggestedFixes,
      patternDetected: result.patternDetected,
      impactAssessment: result.impactAssessment,
      time: result.time
    });
  } catch (error) {
    console.error('Error analyzing counterexamples:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during counterexample analysis',
      message: error.message
    });
  }
};

/**
 * Verify a program with adaptive timeout
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.verifyWithAdaptiveTimeout = async (req, res) => {
  try {
    const { program, ast, options } = req.body;
    
    if (!program && !ast) {
      return res.status(400).json({
        success: false,
        error: 'Either program code or AST is required'
      });
    }
    
    // Extract adaptive timeout options
    const verificationOptions = {
      initialTimeout: options?.initialTimeout || 1000,
      maxTimeout: options?.maxTimeout || 30000,
      timeoutMultiplier: options?.timeoutMultiplier || 2,
      useIncrementalSolving: options?.useIncrementalSolving !== false,
      optimizeConstraints: options?.optimizeConstraints !== false,
      optimizeArrays: options?.optimizeArrays !== false,
      ...options
    };
    
    // Parse the program if AST is not provided
    let programAst = ast;
    if (!programAst && program) {
      try {
        programAst = { type: 'Program', body: [] };
        // programAst = await parserService.parse(program);
      } catch (parseError) {
        return res.status(400).json({
          success: false,
          error: `Parser error: ${parseError.message}`
        });
      }
    }
    
    // Verify with adaptive timeout
    const result = await verificationService.verifyWithAdaptiveTimeout(
      programAst,
      verificationOptions
    );
    
    // Check if verification was successful
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error || 'Verification with adaptive timeout failed'
      });
    }
    
    // Return the verification results
    return res.status(200).json({
      success: true,
      verified: result.verified,
      status: result.status,
      message: result.message,
      counterexamples: result.counterexamples || [],
      timedOut: result.timedOut || false,
      adaptiveTimeout: result.adaptiveTimeout,
      time: result.time
    });
  } catch (error) {
    console.error('Error during verification with adaptive timeout:', error);
    return res.status(500).json({
      success: false,
      error: 'Internal server error during verification',
      message: error.message
    });
  }
};

/**
 * Set verification performance options
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.setVerificationOptions = async (req, res) => {
  try {
    const { options } = req.body;
    
    if (!options || typeof options !== 'object') {
      return res.status(400).json({
        success: false,
        error: 'Options object is required'
      });
    }
    
    // Update default options in the verification service
    verificationService.setDefaultOptions(options);
    
    return res.status(200).json({
      success: true,
      message: 'Verification options updated successfully',
      options: verificationService.defaultOptions
    });
  } catch (error) {
    console.error('Error setting verification options:', error);
    return res.status(500).json({
      success: false,
      error: 'Error setting verification options',
      message: error.message
    });
  }
};

/**
 * Optimize constraints for testing/debugging
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.optimizeConstraints = async (req, res) => {
  try {
    const { constraints, options } = req.body;
    
    if (!constraints || !constraints.assertions) {
      return res.status(400).json({
        success: false,
        error: 'Valid constraint object is required'
      });
    }
    
    // Get optimized constraints from verification service
    const optimizedConstraints = await verificationService.generateConstraints(
      constraints,
      {
        optimizeConstraints: true,
        optimizeArrays: options?.optimizeArrays !== false,
        ...options
      }
    );
    
    // Calculate optimization metrics
    const metrics = {
      originalSize: JSON.stringify(constraints).length,
      optimizedSize: JSON.stringify(optimizedConstraints).length,
      originalAssertions: constraints.assertions.length,
      optimizedAssertions: optimizedConstraints.assertions.length,
      reductionPercentage: 0
    };
    
    // Calculate reduction percentage
    if (metrics.originalSize > 0) {
      metrics.reductionPercentage = 
        ((metrics.originalSize - metrics.optimizedSize) / metrics.originalSize) * 100;
    }
    
    return res.status(200).json({
      success: true,
      originalConstraints: constraints,
      optimizedConstraints: optimizedConstraints,
      metrics: metrics
    });
  } catch (error) {
    console.error('Error optimizing constraints:', error);
    return res.status(500).json({
      success: false,
      error: 'Error optimizing constraints',
      message: error.message
    });
  }
};
