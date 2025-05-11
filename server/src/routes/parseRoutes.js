/**
 * Parse Routes
 * API endpoints for parsing programs into AST
 */
const express = require('express');
const router = express.Router();
const parserService = require('../services/parserService');
const ssaService = require('../services/ssaService');

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
    
    // Parse the program code - use parseProgram instead of parse
    const result = await parserService.parseProgram(programCode, options);
    
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
 * Transform program code or AST to SSA form
 * POST /api/parse/transform-ssa
 * 
 * Request body:
 * {
 *   programCode: string, // Program code to transform (or use ast)
 *   ast: Object,         // AST to transform (alternative to programCode)
 *   loopUnrollingDepth: number // Loop unrolling depth (optional, default 5)
 * }
 * 
 * Response:
 * {
 *   success: boolean,    // Whether transformation was successful
 *   ssaAst: Object,      // AST in SSA form if successful
 *   ssaCode: string,     // String representation of SSA code
 *   optimizedSsaCode: string, // Optimized SSA code
 *   error: string        // Error message if transformation failed
 * }
 */
router.post('/transform-ssa', async (req, res) => {
  try {
    console.log('SSA Transform Request Body:', JSON.stringify(req.body));
    const { programCode, ast, loopUnrollingDepth = 5 } = req.body;
    
    // Ensure we have either program code or AST
    if (!programCode && !ast) {
      return res.status(400).json({
        success: false,
        error: 'Either program code or AST is required'
      });
    }
    
    let result;
    
    // If program code is provided, parse it and then transform
    if (programCode) {
      console.log('Transforming from program code, length:', programCode.length);
      result = await ssaService.parseAndTransformToSSA(programCode, { loopUnrollingDepth });
    } else {
      // Otherwise, transform the provided AST
      console.log('Transforming from AST:', typeof ast);
      result = await ssaService.transformToSSA(ast, { loopUnrollingDepth });
    }
    
    if (result.success) {
      // Fix: Map ssaAST property to ssaAst for client compatibility
      const response = {
        success: true,
        // Use result.ssaAst if it exists, otherwise use result.ssaAST
        ssaAst: result.ssaAst || result.ssaAST, 
        ssaCode: result.ssaCode,
        optimizedSsaCode: result.optimizedSsaCode
      };
      
      console.log('SSA Transform Success:', JSON.stringify(response).substring(0, 100) + '...');
      return res.status(200).json(response);
    } else {
      console.error('SSA Transform Error:', result.error);
      return res.status(400).json({
        success: false,
        error: result.error
      });
    }
  } catch (error) {
    console.error('Error transforming to SSA:', error);
    return res.status(500).json({
      success: false,
      error: `Error transforming to SSA: ${error.message}`
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
    
    // Validate the program code - use validateProgram instead of validate
    const result = await parserService.validateProgram(programCode);
    
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
    
    // Parse the program code - use parseProgram instead of parse
    const result = await parserService.parseProgram(programCode);
    
    if (!result.success) {
      return res.status(400).json({
        success: false,
        error: result.error,
        location: result.location
      });
    }
    
    // Generate visualization - use visualizeAST instead of visualize
    const visualization = parserService.visualizeAST(result.ast, format);
    
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
