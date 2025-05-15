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
    console.log('Received SMT generation request:', JSON.stringify(req.body));
    
    // Get program from request body, support multiple naming conventions
    // First try the standard names (program/programCode)
    let program = req.body.program || req.body.programCode;
    let secondProgram = req.body.secondProgram || req.body.secondProgramCode;
    const options = req.body.options || {};
    const mode = req.body.mode;
    
    // Then try the alternative names used by the client (program1/program2)
    if (!program && req.body.program1) {
      program = req.body.program1;
      
      // If we're in equivalence mode, check for program2
      if (mode === 'equivalence' && req.body.program2) {
        secondProgram = req.body.program2;
      }
    }
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program code is required',
        error: 'Missing program code'
      });
    }

    try {
      // Parse the program
      const parseResult = await parserService.parseProgram(program);
      
      if (!parseResult.success) {
        return res.status(400).json({
          success: false,
          message: `Parser error: ${parseResult.error}`,
          error: parseResult.error
        });
      }
      
      // Transform to SSA
      const ssaResult = await ssaService.transformToSSA(parseResult.ast, options);
      
      if (!ssaResult.success) {
        return res.status(400).json({
          success: false,
          message: `SSA transformation error: ${ssaResult.error}`,
          error: ssaResult.error
        });
      }
      
      let smtConstraints;
      
      // Handle equivalence checking case
      if (secondProgram && (mode === 'equivalence' || req.body.isEquivalence)) {
        // Parse the second program
        const secondParseResult = await parserService.parseProgram(secondProgram);
        
        if (!secondParseResult.success) {
          return res.status(400).json({
            success: false,
            message: `Parser error in second program: ${secondParseResult.error}`,
            error: secondParseResult.error
          });
        }
        
        // Transform second program to SSA
        const secondSsaResult = await ssaService.transformToSSA(secondParseResult.ast, options);
        
        if (!secondSsaResult.success) {
          return res.status(400).json({
            success: false,
            message: `SSA transformation error in second program: ${secondSsaResult.error}`,
            error: secondSsaResult.error
          });
        }
        
        // Generate SMT constraints for equivalence checking
        const constraintsResult = await smtGenerationService.generateConstraintsForEquivalence(
          ssaResult.ssaAst,
          secondSsaResult.ssaAst,
          options
        );
        
        if (!constraintsResult.success) {
          return res.status(400).json({
            success: false,
            message: `Error generating equivalence constraints: ${constraintsResult.error}`,
            error: constraintsResult.error
          });
        }
        
        // Extract constraints from result
        smtConstraints = constraintsResult.smtScript;
      } else {
        // Generate SMT constraints for verification
        const constraintsResult = await smtGenerationService.generateConstraints(ssaResult.ssaAst, options);
        
        if (!constraintsResult.success) {
          return res.status(400).json({
            success: false,
            message: `Error generating constraints: ${constraintsResult.error}`,
            error: constraintsResult.error
          });
        }
        
        // Extract constraints string from result
        smtConstraints = constraintsResult.smtScript;
      }
      
      // Return the SMT constraints
      return res.json({
        success: true,
        smtConstraints: smtConstraints
      });
    } catch (error) {
      console.error('Error in SMT generation process:', error);
      return res.status(500).json({
        success: false,
        message: `Error generating SMT constraints: ${error.message}`,
        error: error.message
      });
    }
  } catch (error) {
    console.error('Error handling SMT generation request:', error);
    return res.status(500).json({
      success: false,
      message: `Error generating SMT constraints: ${error.message}`,
      error: error.message
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
