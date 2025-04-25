/**
 * SMT Routes
 * API endpoints for SMT generation
 */
const express = require('express');
const smtController = require('../controllers/smtController');

const router = express.Router();

// Generate SMT constraints from a program
router.post('/generate', smtController.generateSMT);

// Get example SMT constraints
router.get('/examples', smtController.getExamples);

// Generate SMT for array operations
router.post('/array', smtController.generateArraySMT);

module.exports = router;
