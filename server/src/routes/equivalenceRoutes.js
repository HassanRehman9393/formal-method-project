/**
 * Equivalence checking routes
 * Provides API endpoints for checking semantic equivalence between programs
 */
const express = require('express');
const router = express.Router();
const EquivalenceService = require('../services/equivalenceService');
const equivalenceService = new EquivalenceService(); // Instantiate the class
const smtController = require('../controllers/smtController');

/**
 * Generate SMT constraints for equivalence checking
 * POST /api/equivalence/generate-smt
 */
router.post('/generate-smt', smtController.generateSMT);

/**
 * Check if two programs are semantically equivalent (root endpoint)
 * POST /api/equivalence
 */
router.post('/', async (req, res) => {
  try {
    const { program1, program2, options } = req.body;
    
    if (!program1 || !program2) {
      return res.status(400).json({
        success: false,
        message: 'Both program1 and program2 must be provided'
      });
    }
    
    // Perform equivalence checking
    const result = await equivalenceService.checkEquivalence(program1, program2, options);
    
    res.json(result);
  } catch (error) {
    console.error('Error in equivalence endpoint:', error);
    res.status(500).json({
      success: false,
      message: `Error checking equivalence: ${error.message}`
    });
  }
});

/**
 * Check if two programs are semantically equivalent
 * POST /api/equivalence/check
 * 
 * Request body:
 * {
 *   program1: string or AST or constraints,
 *   program2: string or AST or constraints,
 *   options: {
 *     loopUnrollDepth: number,  // Optional, default 5
 *     includeArrays: boolean,   // Optional, default true
 *     outputs: Array,           // Optional, list of output variables to compare
 *     arrayOutputs: Array       // Optional, list of array output variables
 *   }
 * }
 * 
 * Response:
 * {
 *   success: boolean,           // Whether the operation completed successfully
 *   equivalent: boolean,        // Whether the programs are equivalent
 *   status: string,             // Human-readable status message
 *   counterexample: Object      // If not equivalent, inputs that show the difference
 * }
 */
router.post('/check', async (req, res) => {
  try {
    const { program1, program2, options } = req.body;
    
    if (!program1 || !program2) {
      return res.status(400).json({
        success: false,
        message: 'Both program1 and program2 must be provided'
      });
    }
    
    // Perform equivalence checking
    const result = await equivalenceService.checkEquivalence(program1, program2, options);
    
    res.json(result);
  } catch (error) {
    console.error('Error in equivalence endpoint:', error);
    res.status(500).json({
      success: false,
      message: `Error checking equivalence: ${error.message}`
    });
  }
});

module.exports = router;
