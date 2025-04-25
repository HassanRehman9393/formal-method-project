/**
 * Verification Router
 * Handles API endpoints for program verification and equivalence checking
 */
const express = require('express');
const router = express.Router();
const verificationService = require('../services/verificationService');

/**
 * Verify a program's assertions
 * POST /api/verify
 */
router.post('/', async (req, res) => {
  try {
    const { program, options } = req.body;
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program is required'
      });
    }
    
    const result = await verificationService.verifyProgram(program, options || {});
    return res.json(result);
  } catch (error) {
    console.error('Error in verification endpoint:', error);
    return res.status(500).json({
      success: false,
      message: `Server error: ${error.message}`
    });
  }
});

/**
 * Check equivalence between two programs
 * POST /api/verify/equivalence
 */
router.post('/equivalence', async (req, res) => {
  try {
    const { program1, program2, options } = req.body;
    
    if (!program1 || !program2) {
      return res.status(400).json({
        success: false,
        message: 'Both programs are required'
      });
    }
    
    const result = await verificationService.checkEquivalence(program1, program2, options || {});
    return res.json(result);
  } catch (error) {
    console.error('Error in equivalence endpoint:', error);
    return res.status(500).json({
      success: false,
      message: `Server error: ${error.message}`
    });
  }
});

/**
 * Generate counterexamples for a program
 * POST /api/verify/counterexamples
 */
router.post('/counterexamples', async (req, res) => {
  try {
    const { program, options } = req.body;
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program is required'
      });
    }
    
    const result = await verificationService.generateCounterexamples(program, options || {});
    return res.json(result);
  } catch (error) {
    console.error('Error in counterexamples endpoint:', error);
    return res.status(500).json({
      success: false,
      message: `Server error: ${error.message}`
    });
  }
});

/**
 * Generate SMT constraints for a program
 * POST /api/verify/constraints
 */
router.post('/constraints', (req, res) => {
  try {
    const { program, options } = req.body;
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program is required'
      });
    }
    
    const constraints = verificationService.generateConstraints(program, options || {});
    return res.json({
      success: true,
      constraints,
      time: new Date().toISOString()
    });
  } catch (error) {
    console.error('Error in constraints endpoint:', error);
    return res.status(500).json({
      success: false,
      message: `Server error: ${error.message}`
    });
  }
});

/**
 * Verify if a program satisfies a postcondition
 * POST /api/verify/postcondition
 */
router.post('/postcondition', async (req, res) => {
  try {
    const { program, postcondition, options } = req.body;
    
    if (!program || !postcondition) {
      return res.status(400).json({
        success: false,
        message: 'Both program and postcondition are required'
      });
    }
    
    const result = await verificationService.verifyPostcondition(program, postcondition, options || {});
    return res.json(result);
  } catch (error) {
    console.error('Error in postcondition endpoint:', error);
    return res.status(500).json({
      success: false,
      message: `Server error: ${error.message}`
    });
  }
});

/**
 * Generate test cases for a program
 * POST /api/verify/tests
 */
router.post('/tests', async (req, res) => {
  try {
    const { program, options } = req.body;
    
    if (!program) {
      return res.status(400).json({
        success: false,
        message: 'Program is required'
      });
    }
    
    const result = await verificationService.generateTests(program, options || {});
    return res.json(result);
  } catch (error) {
    console.error('Error in test generation endpoint:', error);
    return res.status(500).json({
      success: false,
      message: `Server error: ${error.message}`
    });
  }
});

module.exports = router;
