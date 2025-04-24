const express = require('express');
const router = express.Router();

// Import route modules (to be implemented later)
const verifyRoutes = require('./verify');
const equivalenceRoutes = require('./equivalence');
const testZ3Routes = require('./test-z3');

// Mount route modules
router.use('/verify', verifyRoutes);
router.use('/equivalence', equivalenceRoutes);
router.use('/test-z3', testZ3Routes);

// Basic test endpoint
router.get('/ping', (req, res) => {
  res.json({ message: 'API is working' });
});

module.exports = router;
