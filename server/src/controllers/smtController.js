/**
 * SMT Controller
 * Handles generation of SMT constraints and interaction with SMT solvers
 */
const parserService = require('../services/parserService');
const ssaService = require('../services/ssaService');
const smtGenerationService = require('../services/smtGenerationService');

/**
 * Generate SMT constraints from a program
 * Handles both verification and equivalence checking cases
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const generateSMT = async (req, res) => {
  try {
    // Get program from request body, support both naming conventions
    const program = req.body.program || req.body.programCode;
    const secondProgram = req.body.secondProgram || req.body.secondProgramCode;
    const options = req.body.options || {};
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program code is required'
      });
    }

    // Parse the program to get AST
    const ast = parserService.parseProgram(program);
    
    // Transform to SSA if requested
    const ssaAst = options.useSSA ? ssaService.transformToSSA(ast) : ast;
    
    let smtConstraints;
    
    // Handle equivalence checking case
    if (secondProgram) {
      // Parse the second program
      const secondAst = parserService.parseProgram(secondProgram);
      
      // Transform to SSA if requested
      const secondSsaAst = options.useSSA ? ssaService.transformToSSA(secondAst) : secondAst;
      
      // Generate SMT constraints for equivalence checking
      smtConstraints = smtGenerationService.generateConstraintsForEquivalence(
        ssaAst,
        secondSsaAst,
        options
      );
    } else {
      // Generate SMT constraints for verification
      smtConstraints = smtGenerationService.generateConstraints(ssaAst, options);
    }
    
    // Return the SMT constraints
    return res.json({
      success: true,
      data: {
        smtConstraints: smtConstraints
      }
    });
  } catch (error) {
    console.error('Error generating SMT constraints:', error);
    return res.status(500).json({
      success: false,
      message: `Error generating SMT constraints: ${error.message}`
    });
  }
};

/**
 * Get example SMT constraints
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const getExamples = (req, res) => {
  try {
    const examples = smtGenerationService.generateExamples();
    
    return res.json({
      success: true,
      data: {
        examples
      }
    });
  } catch (error) {
    console.error('Error getting SMT examples:', error);
    return res.status(500).json({
      success: false,
      message: `Error getting SMT examples: ${error.message}`
    });
  }
};

/**
 * Generate SMT constraints for array operations
 * 
 * @param {Object} req - Express request object
 * @param {Object} res - Express response object
 */
const generateArraySMT = (req, res) => {
  try {
    const { arrays, operations } = req.body;
    
    if (!arrays || !operations) {
      return res.status(400).json({
        success: false,
        message: 'Arrays and operations are required'
      });
    }
    
    const smtScript = smtGenerationService.generateArraySMT(arrays, operations);
    
    return res.json({
      success: true,
      data: {
        smtConstraints: smtScript
      }
    });
  } catch (error) {
    console.error('Error generating array SMT constraints:', error);
    return res.status(500).json({
      success: false,
      message: `Error generating array SMT constraints: ${error.message}`
    });
  }
};

module.exports = {
  generateSMT,
  getExamples,
  generateArraySMT
};
