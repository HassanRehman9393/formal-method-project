/**
 * Parse Routes
 * API endpoints for parsing programs into AST
 */
const express = require('express');
const router = express.Router();
const parserService = require('../services/parserService');

/**
 * Parse program code into AST
 * POST /api/parse
 * 
 * Request body:
 * {
 *   programCode: string,  // Program code to parse
 *   options: {           // Optional parsing options
 *     includeLocations: boolean  // Whether to include source locations in AST
 *   }
 * }
 * 
 * Response:
 * {
 *   success: boolean,    // Whether parsing was successful
 *   ast: Object,         // Abstract Syntax Tree if successful
 *   error: string        // Error message if parsing failed
 * }
 */
router.post('/', async (req, res) => {
  try {
    const { programCode, options } = req.body;
    
    if (!programCode) {
      return res.status(400).json({
        success: false,
        error: 'Program code is required'
      });
    }
    
    // Parse the program code
    const result = await parserService.parse(programCode, options);
    
    if (result.success) {
      return res.status(200).json({
        success: true,
        ast: result.ast
      });
    } else {
      return res.status(400).json({
        success: false,
        error: result.error,
        location: result.location
      });
    }
  } catch (error) {
    console.error('Error parsing program:', error);
    return res.status(500).json({
      success: false,
      error: `Error parsing program: ${error.message}`
    });
  }
});

/**
 * Validate program code syntax without returning full AST
 * POST /api/parse/validate
 * 
 * Request body:
 * {
 *   programCode: string  // Program code to validate
 * }
 * 
 * Response:
 * {
 *   valid: boolean,      // Whether the syntax is valid
 *   error: string        // Error message if validation failed
 * }
 */
router.post('/validate', async (req, res) => {
  try {
    const { programCode } = req.body;
    
    if (!programCode) {
      return res.status(400).json({
        valid: false,
        error: 'Program code is required'
      });
    }
    
    // Validate the program code
    const result = await parserService.validate(programCode);
    
    return res.status(200).json(result);
  } catch (error) {
    console.error('Error validating program:', error);
    return res.status(500).json({
      valid: false,
      error: `Error validating program: ${error.message}`
    });
  }
});

/**
 * Get AST visualization
 * POST /api/parse/visualize
 * 
 * Request body:
 * {
 *   programCode: string,  // Program code to parse
 *   format: string        // Output format (json, html, text)
 * }
 * 
 * Response:
 * {
 *   success: boolean,
 *   visualization: string|Object  // Visualization result
 * }
 */
router.post('/visualize', async (req, res) => {
  try {
    const { programCode, format = 'json' } = req.body;
    
    if (!programCode) {
      return res.status(400).json({
        success: false,
        error: 'Program code is required'
      });
    }
    
    // Parse the program code
    const result = await parserService.parse(programCode);
    
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error,
        location: result.location
      });
    }
    
    // Generate visualization
    const visualization = parserService.visualize(result.ast, format);
    
    // Set appropriate content type
    if (format === 'html') {
      res.setHeader('Content-Type', 'text/html');
    } else if (format === 'text') {
      res.setHeader('Content-Type', 'text/plain');
    } else {
      res.setHeader('Content-Type', 'application/json');
    }
    
    // If format is not JSON, send as is, otherwise wrap in JSON response
    if (format === 'html' || format === 'text') {
      return res.status(200).send(visualization);
    } else {
      return res.status(200).json({
        success: true,
        visualization
      });
    }
  } catch (error) {
    console.error('Error visualizing AST:', error);
    return res.status(500).json({
      success: false,
      error: `Error visualizing AST: ${error.message}`
    });
  }
});

module.exports = router;
