const express = require('express');
const router = express.Router();
const z3Service = require('../services/z3Service');

/**
 * @route POST /api/equivalence
 * @description Check if two programs are semantically equivalent
 * @access Public
 */
router.post('/', async (req, res) => {
  try {
    const { program1, program2 } = req.body;
    
    if (!program1 || !program2) {
      return res.status(400).json({ 
        success: false, 
        message: 'Two programs are required for equivalence checking' 
      });
    }
    
    // Call the Z3 service to check equivalence
    const result = await z3Service.checkEquivalence(program1, program2);
    
    res.json(result);
  } catch (error) {
    res.status(400).json({ success: false, message: error.message });
  }
});

module.exports = router;
