/**
 * Constant Propagation Optimization
 * 
 * Identifies variables that are assigned constant values and propagates 
 * those values to their uses
 */

import { DataFlowAnalysis, DataFlowDirection, JoinOperation } from './dataFlowAnalysis.js';
import { buildSSAGraph } from './ssaGraph.js';

// Lattice values for constant propagation
const Lattice = {
  UNDEFINED: 'undefined',  // Variable has not been defined yet
  CONSTANT: 'constant',    // Variable has a known constant value
  NAC: 'not-a-constant'    // Variable is not a constant
};

// Add a debug flag at the top
const DEBUG = true;

/**
 * Constant propagation data flow analysis
 */
class ConstantPropagationAnalysis extends DataFlowAnalysis {
  constructor() {
    super(DataFlowDirection.FORWARD, JoinOperation.INTERSECTION);
  }
  
  /**
   * Initial value for each block is an empty map
   */
  initialValue(node) {
    // Entry block starts with no known values
    return new Map();
  }
  
  /**
   * Default value is undefined lattice value
   */
  defaultValue() {
    return { state: Lattice.UNDEFINED };
  }
  
  /**
   * Join two lattice values
   */
  joinSingleValue(val1, val2) {
    // If either value is NAC, the result is NAC
    if (val1.state === Lattice.NAC || val2.state === Lattice.NAC) {
      return { state: Lattice.NAC };
    }
    
    // If either value is UNDEFINED, use the other value
    if (val1.state === Lattice.UNDEFINED) {
      return val2;
    }
    if (val2.state === Lattice.UNDEFINED) {
      return val1;
    }
    
    // Both are CONSTANT - if values match, keep the constant, otherwise NAC
    if (val1.value === val2.value) {
      return { state: Lattice.CONSTANT, value: val1.value };
    }
    
    return { state: Lattice.NAC };
  }
  
  /**
   * Join two maps of variable values
   * @param {Map} map1 - First map
   * @param {Map} map2 - Second map
   * @returns {Map} Joined map
   */
  join(map1, map2) {
    const result = new Map();
    
    // Include all variables from both maps
    const allVars = new Set([...map1.keys(), ...map2.keys()]);
    
    for (const varName of allVars) {
      const val1 = map1.get(varName) || this.defaultValue();
      const val2 = map2.get(varName) || this.defaultValue();
      result.set(varName, this.joinSingleValue(val1, val2));
    }
    
    return result;
  }
  
  /**
   * Apply the transfer function to propagate constants
   * @param {SSAGraphNode} node - Current node
   * @param {Map} inputMap - Input value map
   * @returns {Map} Output value map
   */
  transferFunction(node, inputMap, graph) {
    // Create a new map to avoid modifying the input
    const outputMap = new Map(inputMap);
    
    // Process phi functions first
    for (const phi of node.phiFunctions) {
      if (!phi.target) continue;
      
      // Join values from all phi sources
      const sourceValues = [];
      for (const source of phi.sources) {
        const value = inputMap.get(source) || this.defaultValue();
        sourceValues.push(value);
      }
      
      // Combine source values
      let phiResult = sourceValues[0] || this.defaultValue();
      for (let i = 1; i < sourceValues.length; i++) {
        phiResult = this.joinSingleValue(phiResult, sourceValues[i]);
      }
      
      outputMap.set(phi.target, phiResult);
    }
    
    // Process instructions
    for (const instr of node.instructions) {
      if (instr.type === 'Assignment' && instr.target) {
        // Evaluate the right-hand side
        const value = this.evaluateExpression(instr.value, outputMap);
        outputMap.set(instr.target, value);
      }
    }
    
    return outputMap;
  }
  
  /**
   * Evaluate an expression to determine if it's constant
   * @param {object} expr - Expression to evaluate
   * @param {Map} valueMap - Current variable values
   * @returns {object} Lattice value
   */
  evaluateExpression(expr, valueMap) {
    if (!expr) {
      return { state: Lattice.NAC };
    }
    
    if (DEBUG) {
      console.log(`DEBUG evaluateExpression: ${expr.type}`, 
        expr.type === 'Variable' || expr.type === 'Identifier' ? 
        `name=${expr.name}, ssaVersion=${expr.ssaVersion}` : '');
    }
    
    switch (expr.type) {
      case 'IntegerLiteral':
        if (DEBUG) console.log(`DEBUG found IntegerLiteral: ${expr.value}`);
        return { state: Lattice.CONSTANT, value: expr.value };
        
      case 'BooleanLiteral':
        if (DEBUG) console.log(`DEBUG found BooleanLiteral: ${expr.value}`);
        return { state: Lattice.CONSTANT, value: expr.value };
        
      case 'Variable':
      case 'Identifier':
        // Try both with and without ssaVersion
        let varName = expr.name;
        let result = valueMap.get(varName); 
        
        if (DEBUG) {
          console.log(`DEBUG Variable lookup: ${varName} -> ${result ? result.state : 'not found'}`);
        }
        
        // Try with SSA version if available
        if (expr.ssaVersion !== undefined) {
          let ssaName = `${expr.name}_${expr.ssaVersion}`;
          let ssaResult = valueMap.get(ssaName);
          
          if (DEBUG) {
            console.log(`DEBUG SSA lookup: ${ssaName} -> ${ssaResult ? ssaResult.state : 'not found'}`);
          }
          
          if (ssaResult) {
            result = ssaResult;
          }
        }
        
        return result || this.defaultValue();
        
      case 'BinaryExpression':
        const left = this.evaluateExpression(expr.left, valueMap);
        const right = this.evaluateExpression(expr.right, valueMap);
        
        // If either operand is not a constant, the result is not a constant
        if (left.state !== Lattice.CONSTANT || right.state !== Lattice.CONSTANT) {
          return { state: Lattice.NAC };
        }
        
        // Evaluate the operation
        let value;
        switch (expr.operator) {
          case '+': value = left.value + right.value; break;
          case '-': value = left.value - right.value; break;
          case '*': value = left.value * right.value; break;
          case '/': 
            if (right.value === 0) return { state: Lattice.NAC };
            value = Math.floor(left.value / right.value); 
            break;
          case '%': 
            if (right.value === 0) return { state: Lattice.NAC };
            value = left.value % right.value; 
            break;
          case '<': value = left.value < right.value; break;
          case '<=': value = left.value <= right.value; break;
          case '>': value = left.value > right.value; break;
          case '>=': value = left.value >= right.value; break;
          case '==': value = left.value === right.value; break;
          case '!=': value = left.value !== right.value; break;
          case '&&': value = left.value && right.value; break;
          case '||': value = left.value || right.value; break;
          default: return { state: Lattice.NAC };
        }
        
        return { state: Lattice.CONSTANT, value };
        
      case 'UnaryExpression':
        const operand = this.evaluateExpression(expr.operand, valueMap);
        if (operand.state !== Lattice.CONSTANT) {
          return { state: Lattice.NAC };
        }
        
        switch (expr.operator) {
          case '-': return { state: Lattice.CONSTANT, value: -operand.value };
          case '!': return { state: Lattice.CONSTANT, value: !operand.value };
          default: return { state: Lattice.NAC };
        }
        
      default:
        return { state: Lattice.NAC };
    }
  }
  
  /**
   * Check if two maps are equal
   * @param {Map} map1 - First map
   * @param {Map} map2 - Second map
   * @returns {boolean} True if equal
   */
  equals(map1, map2) {
    if (map1 === map2) return true;
    if (!map1 || !map2) return false;
    if (map1.size !== map2.size) return false;
    
    for (const [key, val1] of map1) {
      const val2 = map2.get(key);
      
      // Check if values are the same
      if (!val2) return false;
      if (val1.state !== val2.state) return false;
      if (val1.state === Lattice.CONSTANT && val1.value !== val2.value) return false;
    }
    
    return true;
  }
}

/**
 * Propagate constants in an SSA program
 * @param {object} ssaProgram - The SSA program to optimize
 * @returns {object} Optimized SSA program
 */
export function propagateConstants(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) {
    return ssaProgram; // Return unmodified program if invalid
  }
  
  // Create a deep clone to avoid modifying the original
  const optimizedProgram = JSON.parse(JSON.stringify(ssaProgram));
  
  // Step 1: Build a map of all constants
  const constants = new Map();
  
  // Pre-scan all blocks for constants
  for (const block of optimizedProgram.blocks) {
    if (!block || !block.instructions) continue;
    
    for (const instr of block.instructions) {
      if (instr?.type === 'Assignment') {
        // Direct constant assignments
        if (instr.value?.type === 'IntLiteral' || instr.value?.type === 'IntegerLiteral' || 
            instr.value?.type === 'BoolLiteral' || instr.value?.type === 'BooleanLiteral') {
          constants.set(instr.target, instr.value.value);
        }
      }
    }
  }
  
  // Step 2: Propagate constants
  let optimizationsApplied = false;
  let constantsPropagated = 0;
  
  for (const block of optimizedProgram.blocks) {
    if (!block || !block.instructions) continue;
    
    for (let i = 0; i < block.instructions.length; i++) {
      const instr = block.instructions[i];
      if (!instr || instr.type !== 'Assignment') continue;
      
      // Skip if this is directly a constant
      if (instr.value?.type === 'IntLiteral' || instr.value?.type === 'IntegerLiteral' ||
          instr.value?.type === 'BoolLiteral' || instr.value?.type === 'BooleanLiteral') continue;
      
      // Look for binary expressions where both operands are constants
      if (instr.value?.type === 'BinaryExpression') {
        const expr = instr.value;
        
        let leftValue = null;
        let rightValue = null;
        
        // Get left operand value
        if (expr.left?.type === 'Identifier' || expr.left?.type === 'Variable') {
          const varName = expr.left.name;
          
          // Try with SSA version if available
          let lookupName = varName;
          if (expr.left.ssaVersion !== undefined) {
            lookupName = `${varName}_${expr.left.ssaVersion}`;
          }
          
          if (constants.has(lookupName)) {
            leftValue = constants.get(lookupName);
          } else if (constants.has(varName)) {
            leftValue = constants.get(varName);
          }
          
        } else if (expr.left?.type === 'IntLiteral' || expr.left?.type === 'IntegerLiteral' ||
                  expr.left?.type === 'BoolLiteral' || expr.left?.type === 'BooleanLiteral') {
          leftValue = expr.left.value;
        }
        
        // Get right operand value
        if (expr.right?.type === 'Identifier' || expr.right?.type === 'Variable') {
          const varName = expr.right.name;
          
          // Try with SSA version if available
          let lookupName = varName;
          if (expr.right.ssaVersion !== undefined) {
            lookupName = `${varName}_${expr.right.ssaVersion}`;
          }
          
          if (constants.has(lookupName)) {
            rightValue = constants.get(lookupName);
          } else if (constants.has(varName)) {
            rightValue = constants.get(varName);
          }
          
        } else if (expr.right?.type === 'IntLiteral' || expr.right?.type === 'IntegerLiteral' ||
                  expr.right?.type === 'BoolLiteral' || expr.right?.type === 'BooleanLiteral') {
          rightValue = expr.right.value;
        }
        
        // If both operands are constants, fold the expression
        if (leftValue !== null && rightValue !== null) {
          let resultValue;
          switch (expr.operator) {
            case '+': resultValue = leftValue + rightValue; break;
            case '-': resultValue = leftValue - rightValue; break;
            case '*': resultValue = leftValue * rightValue; break;
            case '/': resultValue = rightValue !== 0 ? Math.floor(leftValue / rightValue) : null; break;
            case '%': resultValue = rightValue !== 0 ? leftValue % rightValue : null; break;
            case '<': resultValue = leftValue < rightValue; break;
            case '<=': resultValue = leftValue <= rightValue; break;
            case '>': resultValue = leftValue > rightValue; break;
            case '>=': resultValue = leftValue >= rightValue; break;
            case '==': resultValue = leftValue === rightValue; break;
            case '!=': resultValue = leftValue !== rightValue; break;
            case '&&': resultValue = leftValue && rightValue; break;
            case '||': resultValue = leftValue || rightValue; break;
            default: resultValue = null;
          }
          
          if (resultValue !== null) {
            // Get the correct type for the literal
            const type = typeof resultValue === 'boolean' ? 'BooleanLiteral' : 'IntegerLiteral';
            
            // Replace with optimized constant
            block.instructions[i] = {
              ...instr,
              value: { type, value: resultValue },
              optimized: true,
              optimizationType: 'ConstantPropagation',
              originalValue: JSON.parse(JSON.stringify(instr.value))
            };
            
            optimizationsApplied = true;
            constantsPropagated++;
            
            // Add to constants map for further propagation
            constants.set(instr.target, resultValue);
          }
        }
      }
      
      // Handle unary expressions
      if (instr.value?.type === 'UnaryExpression') {
        const expr = instr.value;
        
        let operandValue = null;
        
        // Get operand value
        if (expr.operand?.type === 'Identifier' || expr.operand?.type === 'Variable') {
          const varName = expr.operand.name;
          
          // Try with SSA version if available
          let lookupName = varName;
          if (expr.operand.ssaVersion !== undefined) {
            lookupName = `${varName}_${expr.operand.ssaVersion}`;
          }
          
          if (constants.has(lookupName)) {
            operandValue = constants.get(lookupName);
          } else if (constants.has(varName)) {
            operandValue = constants.get(varName);
          }
          
        } else if (expr.operand?.type === 'IntLiteral' || expr.operand?.type === 'IntegerLiteral' ||
                  expr.operand?.type === 'BoolLiteral' || expr.operand?.type === 'BooleanLiteral') {
          operandValue = expr.operand.value;
        }
        
        // If operand is a constant, fold the expression
        if (operandValue !== null) {
          let resultValue;
          switch (expr.operator) {
            case '-': resultValue = -operandValue; break;
            case '!': resultValue = !operandValue; break;
            default: resultValue = null;
          }
          
          if (resultValue !== null) {
            // Get the correct type for the literal
            const type = typeof resultValue === 'boolean' ? 'BooleanLiteral' : 'IntegerLiteral';
            
            // Replace with optimized constant
            block.instructions[i] = {
              ...instr,
              value: { type, value: resultValue },
              optimized: true,
              optimizationType: 'ConstantPropagation',
              originalValue: JSON.parse(JSON.stringify(instr.value))
            };
            
            optimizationsApplied = true;
            constantsPropagated++;
            
            // Add to constants map for further propagation
            constants.set(instr.target, resultValue);
          }
        }
      }
    }
  }
  
  // Add metadata to indicate if optimizations were applied
  optimizedProgram.metadata = {
    ...optimizedProgram.metadata,
    constantPropagationApplied: optimizationsApplied,
    constantsPropagated
  };
  
  return optimizedProgram;
}

// Add alias for imported name consistency
export const constantPropagation = propagateConstants;

/**
 * Replace variables with known constant values
 * @param {object} expr - Expression to optimize
 * @param {Map} constants - Map of variable names to constant values
 * @returns {object} Optimized expression
 */
function replaceConstants(expr, constants) {
  if (!expr || !constants) return expr;
  
  if (expr.type === 'Variable' || expr.type === 'Identifier') {
    // First try to get by the full variable name (with SSA version)
    let fullVarName = expr.name;
    if (expr.ssaVersion !== undefined) {
      fullVarName = `${expr.name}_${expr.ssaVersion}`;
    }
    
    // Try to get constant value by both the full name and simple name
    let constVal = constants.get(fullVarName);
    if (!constVal) {
      constVal = constants.get(expr.name);
    }
    
    // If variable is a known constant, replace it
    if (constVal && constVal.state === Lattice.CONSTANT) {
      const type = typeof constVal.value === 'boolean' ? 'BooleanLiteral' : 'IntegerLiteral';
      return {
        type,
        value: constVal.value,
        originalVariable: expr.name,
        originalVersion: expr.ssaVersion
      };
    }
    
    return expr;
  }
  
  // Handle binary expressions
  if (expr.type === 'BinaryExpression') {
    const optimizedLeft = replaceConstants(expr.left, constants);
    const optimizedRight = replaceConstants(expr.right, constants);
    
    // Check if both operands are constants, if so, fold the expression
    if ((optimizedLeft.type === 'IntegerLiteral' || optimizedLeft.type === 'BooleanLiteral') &&
        (optimizedRight.type === 'IntegerLiteral' || optimizedRight.type === 'BooleanLiteral')) {
      
      const analysis = new ConstantPropagationAnalysis();
      const result = analysis.evaluateExpression({
        type: 'BinaryExpression',
        operator: expr.operator,
        left: optimizedLeft,
        right: optimizedRight
      }, new Map());
      
      // If we could evaluate to a constant, replace the expression
      if (result.state === Lattice.CONSTANT) {
        const type = typeof result.value === 'boolean' ? 'BooleanLiteral' : 'IntegerLiteral';
        return {
          type,
          value: result.value,
          originalExpression: {
            type: 'BinaryExpression',
            operator: expr.operator,
            left: expr.left,
            right: expr.right
          }
        };
      }
    }
    
    // If only operands changed, create a new expression with the optimized operands
    if (optimizedLeft !== expr.left || optimizedRight !== expr.right) {
      return {
        ...expr,
        left: optimizedLeft,
        right: optimizedRight
      };
    }
  }
  
  // Handle unary expressions
  if (expr.type === 'UnaryExpression') {
    const optimizedOperand = replaceConstants(expr.operand, constants);
    
    // Check if operand is a constant, if so, fold the expression
    if (optimizedOperand.type === 'IntegerLiteral' || optimizedOperand.type === 'BooleanLiteral') {
      const analysis = new ConstantPropagationAnalysis();
      const result = analysis.evaluateExpression({
        type: 'UnaryExpression',
        operator: expr.operator,
        operand: optimizedOperand
      }, new Map());
      
      // If we could evaluate to a constant, replace the expression
      if (result.state === Lattice.CONSTANT) {
        const type = typeof result.value === 'boolean' ? 'BooleanLiteral' : 'IntegerLiteral';
        return {
          type,
          value: result.value,
          originalExpression: {
            type: 'UnaryExpression',
            operator: expr.operator,
            operand: expr.operand
          }
        };
      }
    }
    
    // If only operand changed, create a new expression with the optimized operand
    if (optimizedOperand !== expr.operand) {
      return {
        ...expr,
        operand: optimizedOperand
      };
    }
  }
  
  return expr;
}
