/**
 * Validates request body for program verification
 */
exports.validateVerificationRequest = (req, res, next) => {
  const { program, loopUnrollingDepth } = req.body;
  
  if (!program || typeof program !== 'string') {
    return res.status(400).json({
      success: false,
      error: 'Valid program code is required'
    });
  }

  if (loopUnrollingDepth !== undefined && 
      (typeof loopUnrollingDepth !== 'number' || 
       loopUnrollingDepth < 0 || 
       loopUnrollingDepth > 10)) {
    return res.status(400).json({
      success: false,
      error: 'Loop unrolling depth must be a number between 0 and 10'
    });
  }

  next();
};

/**
 * Validates request body for equivalence checking
 */
exports.validateEquivalenceRequest = (req, res, next) => {
  const { program1, program2, loopUnrollingDepth } = req.body;
  
  if (!program1 || typeof program1 !== 'string') {
    return res.status(400).json({
      success: false,
      error: 'First program code is required'
    });
  }

  if (!program2 || typeof program2 !== 'string') {
    return res.status(400).json({
      success: false,
      error: 'Second program code is required'
    });
  }

  if (loopUnrollingDepth !== undefined && 
      (typeof loopUnrollingDepth !== 'number' || 
       loopUnrollingDepth < 0 || 
       loopUnrollingDepth > 10)) {
    return res.status(400).json({
      success: false,
      error: 'Loop unrolling depth must be a number between 0 and 10'
    });
  }

  next();
};
