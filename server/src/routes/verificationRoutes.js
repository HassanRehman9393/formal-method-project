/**
 * Verification Routes
 * API endpoints for program verification
 */
const express = require('express');
const verificationController = require('../controllers/verificationController');
const performanceMiddleware = require('../middleware/performanceMiddleware');

const router = express.Router();

// Apply global middleware
router.use(performanceMiddleware.optimizeSolverMiddleware);

// Rate-limited and cached verification endpoints
router.post('/verify', 
  performanceMiddleware.rateLimitMiddleware('verify'),
  performanceMiddleware.cacheMiddleware,
  verificationController.verifyProgram
);

// Verify a program in SSA form
router.post('/verify-ssa', 
  performanceMiddleware.rateLimitMiddleware('verify'),
  performanceMiddleware.cacheMiddleware,
  verificationController.verifyFromSSA
);

// Generate verification report
router.post('/report', verificationController.generateReport);

// Check equivalence between two programs
router.post('/equivalence', 
  performanceMiddleware.rateLimitMiddleware('equivalence'),
  performanceMiddleware.cacheMiddleware,
  verificationController.checkEquivalence
);

// Generate enhanced counterexamples with execution traces
router.post('/enhanced-counterexamples', verificationController.generateEnhancedCounterexamples);

// Generate execution trace for a specific counterexample
router.post('/execution-trace', verificationController.generateExecutionTrace);

// Analyze multiple counterexamples to detect patterns
router.post('/analyze-counterexamples', verificationController.analyzeCounterexamples);

// Performance optimization routes
router.post('/verify-adaptive-timeout', 
  performanceMiddleware.rateLimitMiddleware('verify'),
  performanceMiddleware.cacheMiddleware,
  verificationController.verifyWithAdaptiveTimeout
);

router.post('/set-options', verificationController.setVerificationOptions);

router.post('/optimize-constraints', 
  performanceMiddleware.rateLimitMiddleware('optimize'),
  performanceMiddleware.cacheMiddleware,
  verificationController.optimizeConstraints
);

// Performance monitoring and management endpoints
router.get('/performance-stats', performanceMiddleware.getPerformanceStats);
router.post('/clear-cache', performanceMiddleware.clearCache);

module.exports = router;
