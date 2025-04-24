const express = require('express');
const router = express.Router();
const z3Service = require('../services/z3Service');

/**
 * @route GET /api/test-z3/simple
 * @description Run a simple Z3 test
 * @access Public
 */
router.get('/simple', async (req, res) => {
  try {
    const result = await z3Service.runTest();
    res.json(result);
  } catch (error) {
    res.status(500).json({ success: false, message: error.message });
  }
});

/**
 * @route POST /api/test-z3/constraint
 * @description Test Z3 with custom constraint
 * @access Public
 */
router.post('/constraint', async (req, res) => {
  try {
    await z3Service.initialize();
    const { z3, solver } = await z3Service.getContext();
    
    const constraints = req.body.constraints;
    if (!constraints) {
      return res.status(400).json({ 
        success: false, 
        message: 'Constraints are required' 
      });
    }
    
    // Create variables
    const variables = {};
    for (const varDef of constraints.variables || []) {
      if (varDef.type === 'Int') {
        variables[varDef.name] = z3.Int.const(varDef.name);
      } else if (varDef.type === 'Bool') {
        variables[varDef.name] = z3.Bool.const(varDef.name);
      } else if (varDef.type === 'Real') {
        variables[varDef.name] = z3.Real.const(varDef.name);
      }
    }
    
    // Add assertions
    for (const assertion of constraints.assertions || []) {
      // This is simplified - in reality you'd need to parse expressions
      // This example just illustrates the concept
      if (assertion.type === 'gt' && variables[assertion.left] && variables[assertion.right]) {
        solver.add(z3.gt(variables[assertion.left], variables[assertion.right]));
      } else if (assertion.type === 'eq' && variables[assertion.left] && variables[assertion.right]) {
        solver.add(z3.eq(variables[assertion.left], variables[assertion.right]));
      }
      // Add more types as needed
    }
    
    // Check satisfiability
    const result = await solver.check();
    
    if (result === 'sat') {
      // Get the model (solution)
      const model = solver.model();
      const solution = {};
      
      for (const varName in variables) {
        solution[varName] = model.eval(variables[varName]).toString();
      }
      
      res.json({
        success: true,
        result: 'sat',
        solution
      });
    } else {
      res.json({
        success: true,
        result
      });
    }
  } catch (error) {
    res.status(500).json({ success: false, message: error.message });
  }
});

module.exports = router;
