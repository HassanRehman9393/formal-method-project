const express = require('express');
const router = express.Router();
const verificationController = require('../controllers/verificationController');
const smtController = require('../controllers/smtController');

/**
 * @route POST /api/verify
 * @desc Verify assertions in a program
 * @access Public
 */
router.post('/verify', verificationController.verifyProgram);

/**
 * @route POST /api/equivalence
 * @desc Check if two programs are semantically equivalent
 * @access Public
 */
router.post('/equivalence', verificationController.checkEquivalence);

/**
 * @route POST /api/parse
 * @desc Parse program and return AST
 * @access Public
 */
router.post('/parse', verificationController.parseProgram);

/**
 * @route POST /api/smt/generate
 * @desc Generate SMT constraints for a program
 * @access Public
 */
router.post('/smt/generate', smtController.generateSMT);

/**
 * @route GET /api/smt/examples
 * @desc Get example SMT constraints
 * @access Public
 */
router.get('/smt/examples', smtController.getExamples);

module.exports = router;
