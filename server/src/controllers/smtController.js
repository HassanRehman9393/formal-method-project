/**
 * SMT Controller
 * Handles API requests related to SMT generation
 */
const smtGenerationService = require('../services/smtGenerationService');

/**
 * Generate SMT constraints from a program with support for arrays and control flow
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.generateSMT = async (req, res) => {
  try {
    const { program, ast, options } = req.body;
    
    if (!program && !ast) {
      return res.status(400).json({
        success: false,
        error: 'Either program code or AST is required'
      });
    }
    
    // Extract options for constraint generation
    const constraintOptions = {
      loopUnrollDepth: options?.loopUnrollDepth || 5,
      generateArrayConstraints: options?.generateArrayConstraints !== false,
      includeLoopInvariants: options?.includeLoopInvariants !== false
    };
    
    // If we have an AST directly, use it; otherwise we'd need to parse the program
    if (!ast) {
      return res.status(400).json({
        success: false,
        error: 'Parser not implemented yet - please provide AST directly'
      });
    }
    
    const result = await smtGenerationService.generateConstraints(ast, constraintOptions);
    
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error
      });
    }
    
    return res.status(200).json({
      success: true,
      smtScript: result.smtScript,
      declarations: result.declarations,
      assertions: result.assertions,
      variables: result.variables,
      arrays: result.arrays || []
    });
  } catch (error) {
    console.error('Error generating SMT:', error);
    return res.status(500).json({
      success: false,
      error: 'Failed to generate SMT constraints',
      message: error.message
    });
  }
};

/**
 * Get example SMT constraints
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.getExamples = (req, res) => {
  try {
    const examples = smtGenerationService.generateExamples();
    
    return res.status(200).json({
      success: true,
      examples
    });
  } catch (error) {
    console.error('Error generating example SMT:', error);
    return res.status(500).json({
      success: false,
      error: 'Failed to generate example SMT constraints',
      message: error.message
    });
  }
};

/**
 * Generate SMT for array operations
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.generateArraySMT = async (req, res) => {
  try {
    const { arrays, operations } = req.body;
    
    if (!arrays || !operations) {
      return res.status(400).json({
        success: false,
        error: 'Both arrays and operations are required'
      });
    }
    
    // Generate declarations for arrays
    const declarations = smtGenerationService.generateArrayDeclarations(arrays);
    
    // Generate operations for arrays
    const assertions = smtGenerationService.generateArrayOperations(operations);
    
    // Generate final script
    const smtScript = smtGenerationService.generateSMTScript({
      arrays,
      arrayOperations: operations
    });
    
    return res.status(200).json({
      success: true,
      smtScript,
      declarations,
      assertions
    });
  } catch (error) {
    console.error('Error generating array SMT:', error);
    return res.status(500).json({
      success: false,
      error: 'Failed to generate SMT for arrays',
      message: error.message
    });
  }
};
