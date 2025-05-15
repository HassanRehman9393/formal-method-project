const express = require('express');
const cors = require('cors');
const bodyParser = require('body-parser');

// Import routes
const smtRoutes = require('./routes/smtRoutes');
const verificationRoutes = require('./routes/verificationRoutes');
const parseRoutes = require('./routes/parseRoutes');
const equivalenceRoutes = require('./routes/equivalenceRoutes');

// Initialize Z3 service
const Z3Service = require('./services/z3Service');
const z3Service = new Z3Service();

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

// Initialize Z3 service before starting the server
async function startServer() {
  try {
    // Initialize Z3 service
    await z3Service.initialize();
    console.log('Z3 solver initialized successfully');
    
    // Start the server
    const PORT = process.env.PORT || 3002;
    app.listen(PORT, () => {
      console.log(`Server running on port ${PORT}`);
    });
  } catch (error) {
    console.error('Failed to initialize Z3 solver:', error);
    process.exit(1);
  }
}

// Start the server
startServer();

module.exports = app;
