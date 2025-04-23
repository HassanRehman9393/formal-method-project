const express = require('express');
const router = express.Router();

// Import route modules (to be implemented later)
const verifyRoutes = require('./verify');
const equivalenceRoutes = require('./equivalence');

// Mount route modules
router.use('/verify', verifyRoutes);
router.use('/equivalence', equivalenceRoutes);

// Basic test endpoint
router.get('/ping', (req, res) => {
  res.json({ message: 'API is working' });
});

module.exports = router;
