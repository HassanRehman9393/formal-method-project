/**
 * SMT Controller
 * Handles API requests related to SMT generation
 */
const smtGenerationService = require('../services/smtGenerationService');

/**
 * Generate SMT constraints from a program
 * @param {Request} req - Express request object
 * @param {Response} res - Express response object
 */
exports.generateSMT = async (req, res) => {
  try {
    const { program, ast } = req.body;
    
    if (!program && !ast) {
      return res.status(400).json({
        success: false,
        error: 'Either program code or AST is required'
      });
    }
    
    // If we have an AST directly, use it; otherwise we'd need to parse the program
    // Since parsing isn't implemented yet, we'll assume the AST is provided
    if (!ast) {
      return res.status(400).json({
        success: false,
        error: 'Parser not implemented yet - please provide AST directly'
      });
    }
    
    const result = await smtGenerationService.generateConstraints(ast);
    
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
      variables: result.variables
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
