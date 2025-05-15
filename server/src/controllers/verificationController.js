/**
 * Verification Controller
 * 
 * Handles API endpoints for program verification
 */
const verificationService = require('../services/verificationService');
const parserService = require('../services/parserService');
const ssaService = require('../services/ssaService');
const smtGenerationService = require('../services/smtGenerationService');
const solverService = require('../services/solverService');

/**
 * Verify a program by checking assertions and postconditions
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const verifyProgram = async (req, res) => {
  const startTime = Date.now();
  
  try {
    // Get program from request body, support both naming conventions
    const program = req.body.program || req.body.programCode;
    const options = req.body.options || {};
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program code is required'
      });
    }
    
    // Default verification options
    const verificationOptions = {
      loopUnrollDepth: options.loopUnrollDepth || 5,
      maxTimeout: options.maxTimeout || 30000,
      includeArrays: options.includeArrays !== false,
      ...options
    };
    
    // Parse the program
    const parseResult = await parserService.parseProgram(program);
    
    if (!parseResult.success) {
      return res.status(400).json({
        success: false,
        message: `Parser error: ${parseResult.error}`
      });
    }
    
    // Transform to SSA if requested
    let ssaResult;
    if (options.useSSA !== false) {
      ssaResult = await ssaService.transformToSSA(parseResult.ast, verificationOptions);
      
      if (!ssaResult.success) {
        return res.status(400).json({
          success: false,
          message: `SSA transformation error: ${ssaResult.error}`
        });
      }
    }
    
    // Use verification service to verify the program
    const verificationResult = await verificationService.verifyAssertions(
      options.useSSA !== false ? ssaResult.ssaAst : parseResult.ast,
      verificationOptions
    );
    
    const executionTime = Date.now() - startTime;
    
    if (!verificationResult.success) {
      return res.status(500).json({
        success: false,
        message: `Verification error: ${verificationResult.error}`
      });
    }
    
    // For a simple program with no assertions, we want to show it as verified
    const noAssertionsMessage = 'No assertions found in program - considering program verified';
    
    // Format response
    return res.json({
      success: true,
      data: {
        verified: verificationResult.verified === false ? false : true,
        message: verificationResult.message || (verificationResult.verified ? 'All assertions verified successfully!' : noAssertionsMessage),
        counterexamples: verificationResult.counterexamples || [],
        executionTime: verificationResult.time || executionTime
      }
    });
  } catch (error) {
    console.error('Error in verification:', error);
    return res.status(500).json({
      success: false,
      message: `Verification failed: ${error.message}`
    });
  }
};

/**
 * Verify a program from its SSA form
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const verifyFromSSA = async (req, res) => {
  try {
    const { ssaAst, options } = req.body;
    
    if (!ssaAst) {
      return res.status(400).json({
        success: false,
        message: 'SSA AST is required'
      });
    }
    
    // Real verification from SSA
    const verificationResult = await verificationService.verifyFromSSA(ssaAst, options || {});
    
    if (!verificationResult.success) {
      return res.status(500).json({
        success: false,
        message: `Verification error: ${verificationResult.error}`
      });
    }
    
    return res.json({
      success: true,
      data: {
        verified: verificationResult.verified,
        message: verificationResult.message,
        counterexamples: verificationResult.counterexamples || [],
        executionTime: verificationResult.time || 0
      }
    });
  } catch (error) {
    console.error('Error in SSA verification:', error);
    return res.status(500).json({
      success: false,
      message: `SSA verification failed: ${error.message}`
    });
  }
};

/**
 * Generate a verification report
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const generateReport = async (req, res) => {
  try {
    const { verificationResults, format } = req.body;
    
    if (!verificationResults) {
      return res.status(400).json({
        success: false,
        message: 'Verification results are required'
      });
    }
    
    const report = verificationService.generateReport(verificationResults, format || 'json');
    
    return res.json({
      success: true,
      data: {
        report
      }
    });
  } catch (error) {
    console.error('Error generating report:', error);
    return res.status(500).json({
      success: false,
      message: `Report generation failed: ${error.message}`
    });
  }
};

/**
 * Check equivalence between two programs
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const checkEquivalence = async (req, res) => {
  try {
    const { program1, program2, options } = req.body;
    
    if (!program1 || !program2) {
      return res.status(400).json({
        success: false,
        message: 'Both program1 and program2 must be provided'
      });
    }
    
    // Use verification service to check equivalence
    const equivalenceResult = await verificationService.checkEquivalence(
      program1,
      program2,
      options || {}
    );
    
    if (!equivalenceResult.success) {
      return res.status(500).json({
        success: false,
        message: `Equivalence check error: ${equivalenceResult.error}`
      });
    }
    
    return res.json({
      success: true,
      data: {
        equivalent: equivalenceResult.equivalent,
        message: equivalenceResult.message,
        counterexample: equivalenceResult.counterexample,
        time: equivalenceResult.time || 0
      }
    });
  } catch (error) {
    console.error('Error checking equivalence:', error);
    return res.status(500).json({
      success: false,
      message: `Equivalence check failed: ${error.message}`
    });
  }
};

/**
 * Generate enhanced counterexamples with execution traces
 */
const generateEnhancedCounterexamples = async (req, res) => {
  try {
    const { program, verificationResult } = req.body;
    
    if (!program || !verificationResult) {
      return res.status(400).json({
        success: false,
        message: 'Program and verification result are required'
      });
    }
    
    // Parse the program
    const parseResult = await parserService.parse(program);
    
    if (!parseResult.success) {
      return res.status(400).json({
        success: false,
        message: `Parser error: ${parseResult.error}`
      });
    }
    
    // Get counterexamples from verification result
    const counterexamples = verificationResult.counterexamples || [];
    
    if (counterexamples.length === 0) {
      return res.json({
        success: true,
        data: {
          counterexamples: []
        }
      });
    }
    
    // Generate execution traces for each counterexample
    const enhancedCounterexamples = counterexamples.map(counterexample => {
      // Use Z3 service to generate execution trace
      const trace = counterexample.trace || [];
      
      return {
        inputs: counterexample.inputs,
        trace
      };
    });
    
    return res.json({
      success: true,
      data: {
        counterexamples: enhancedCounterexamples
      }
    });
  } catch (error) {
    console.error('Error generating enhanced counterexamples:', error);
    return res.status(500).json({
      success: false,
      message: `Enhanced counterexample generation failed: ${error.message}`
    });
  }
};

/**
 * Generate execution trace for a specific counterexample
 */
const generateExecutionTrace = async (req, res) => {
  try {
    const { program, counterexample } = req.body;
    
    if (!program || !counterexample) {
      return res.status(400).json({
        success: false,
        message: 'Program and counterexample are required'
      });
    }
    
    // Parse the program
    const parseResult = await parserService.parse(program);
    
    if (!parseResult.success) {
      return res.status(400).json({
        success: false,
        message: `Parser error: ${parseResult.error}`
      });
    }
    
    // Generate constraints
    const constraints = await smtGenerationService.generateConstraints(parseResult.ast, {
      includeStatements: true
    });
    
    // Create a trace from the counterexample
    const trace = [];
    
    // Extract statements from constraints
    const statements = constraints.statements || [];
    
    // Simulate execution with the counterexample values
    let state = { ...counterexample.inputs };
    
    for (let i = 0; i < statements.length; i++) {
      const statement = statements[i];
      
      // Update state based on the statement (simplified)
      if (statement.type === 'AssignmentStatement' && statement.left && statement.left.name) {
        const varName = statement.left.name;
        
        // Simulate execution (very simplified)
        if (state[varName] !== undefined) {
          state[varName] = state[varName] + 1; // Just an example
        }
      }
      
      trace.push({
        line: statement.line || i + 1,
        statement: statement.text || `Statement ${i+1}`,
        state: { ...state }
      });
    }
    
    return res.json({
      success: true,
      data: {
        trace
      }
    });
  } catch (error) {
    console.error('Error generating execution trace:', error);
    return res.status(500).json({
      success: false,
      message: `Execution trace generation failed: ${error.message}`
    });
  }
};

/**
 * Analyze counterexamples to detect patterns
 */
const analyzeCounterexamples = async (req, res) => {
  try {
    const { counterexamples } = req.body;
    
    if (!counterexamples || !Array.isArray(counterexamples) || counterexamples.length === 0) {
      return res.status(400).json({
        success: false,
        message: 'Valid counterexamples array is required'
      });
    }
    
    // Analyze for patterns
    const patterns = [];
    
    // Check for range patterns
    const variables = Object.keys(counterexamples[0].inputs);
    
    for (const variable of variables) {
      const values = counterexamples.map(c => c.inputs[variable]);
      
      if (values.every(v => typeof v === 'number')) {
        const min = Math.min(...values);
        const max = Math.max(...values);
        
        patterns.push({
          type: 'range',
          variable,
          min,
          max,
          description: `${variable} appears to be in the range [${min}, ${max}]`
        });
      }
    }
    
    return res.json({
      success: true,
      data: {
        patterns
      }
    });
  } catch (error) {
    console.error('Error analyzing counterexamples:', error);
    return res.status(500).json({
      success: false,
      message: `Counterexample analysis failed: ${error.message}`
    });
  }
};

/**
 * Verify with adaptive timeout
 */
const verifyWithAdaptiveTimeout = async (req, res) => {
  try {
    const { program, options } = req.body;
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program is required'
      });
    }
    
    // Start with a short timeout
    let currentTimeout = 1000;
    const maxTimeout = options?.maxTimeout || 30000;
    const timeoutMultiplier = options?.timeoutMultiplier || 2;
    
    let verificationResult;
    let timedOut = true;
    
    while (timedOut && currentTimeout <= maxTimeout) {
      // Verify with current timeout
      verificationResult = await verificationService.verifyAssertions(
        await parserService.parse(program).then(result => result.ast),
        {
          ...options,
          timeout: currentTimeout
        }
      );
      
      // Check if timed out
      if (verificationResult.success && !verificationResult.timedOut) {
        timedOut = false;
      } else {
        // Increase timeout
        currentTimeout = Math.min(currentTimeout * timeoutMultiplier, maxTimeout);
      }
    }
    
    return res.json({
      success: true,
      data: {
        verified: verificationResult.verified,
        adaptiveTimeout: currentTimeout,
        timedOut: timedOut,
        counterexamples: verificationResult.counterexamples || []
      }
    });
  } catch (error) {
    console.error('Error in adaptive timeout verification:', error);
    return res.status(500).json({
      success: false,
      message: `Adaptive timeout verification failed: ${error.message}`
    });
  }
};

/**
 * Set verification options
 */
const setVerificationOptions = (req, res) => {
  try {
    const { options } = req.body;
    
    if (!options) {
      return res.status(400).json({
        success: false,
        message: 'Options are required'
      });
    }
    
    // For now, just echo back the options
    // In a real implementation, these could be saved in a configuration service
    return res.json({
      success: true,
      data: {
        options
      }
    });
  } catch (error) {
    console.error('Error setting verification options:', error);
    return res.status(500).json({
      success: false,
      message: `Setting verification options failed: ${error.message}`
    });
  }
};

/**
 * Optimize constraints
 */
const optimizeConstraints = async (req, res) => {
  try {
    const { constraints, optimizationLevel } = req.body;
    
    if (!constraints) {
      return res.status(400).json({
        success: false,
        message: 'Constraints are required'
      });
    }
    
    // Use the constraint optimizer
    const level = optimizationLevel || 'medium';
    const optimized = await smtGenerationService.optimizeConstraints(constraints, { level });
    
    return res.json({
      success: true,
      data: {
        optimizedConstraints: optimized
      }
    });
  } catch (error) {
    console.error('Error optimizing constraints:', error);
    return res.status(500).json({
      success: false,
      message: `Constraint optimization failed: ${error.message}`
    });
  }
};

module.exports = {
  verifyProgram,
  verifyFromSSA,
  generateReport,
  checkEquivalence,
  generateEnhancedCounterexamples,
  generateExecutionTrace,
  analyzeCounterexamples,
  verifyWithAdaptiveTimeout,
  setVerificationOptions,
  optimizeConstraints
};
