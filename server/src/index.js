const express = require('express');
const cors = require('cors');
const bodyParser = require('body-parser');

// Import routes
const smtRoutes = require('./routes/smtRoutes');
const verificationRoutes = require('./routes/verificationRoutes');
const parseRoutes = require('./routes/parseRoutes');
const equivalenceRoutes = require('./routes/equivalenceRoutes');

// Initialize the app
const app = express();

// Middleware
app.use(cors());
app.use(bodyParser.json({ limit: '10mb' }));
app.use(bodyParser.urlencoded({ extended: true, limit: '10mb' }));

// Define routes
app.use('/api/smt', smtRoutes);
app.use('/api/verify', verificationRoutes);
app.use('/api/parse', parseRoutes);
app.use('/api/equivalence', equivalenceRoutes);

// Root route
app.get('/', (req, res) => {
  res.send('Formal Methods Program Analyzer API');
});

// Error handling middleware
app.use((err, req, res, next) => {
  console.error('Server error:', err);
  res.status(500).json({
    success: false,
    error: 'Internal server error',
    message: err.message
  });
});

// Start the server
const PORT = process.env.PORT || 3001;
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`);
});

module.exports = app;
