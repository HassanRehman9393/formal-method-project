/**
 * Verification Routes
 * API endpoints for program verification
 */
const express = require('express');
const verificationController = require('../controllers/verificationController');

const router = express.Router();

// Verify a program's assertions
router.post('/verify', verificationController.verifyProgram);

// Verify a program in SSA form
router.post('/verify-ssa', verificationController.verifyFromSSA);

// Generate verification report
router.post('/report', verificationController.generateReport);

// Check equivalence between two programs
router.post('/equivalence', verificationController.checkEquivalence);

module.exports = router;
