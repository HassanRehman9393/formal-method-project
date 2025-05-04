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
    
    switch (expr.type) {
      case 'IntegerLiteral':
        return { state: Lattice.CONSTANT, value: expr.value };
        
      case 'BooleanLiteral':
        return { state: Lattice.CONSTANT, value: expr.value };
        
      case 'Variable':
        return valueMap.get(expr.name) || this.defaultValue();
        
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
  
  // Build SSA graph
  const graph = buildSSAGraph(optimizedProgram);
  
  // Run constant propagation analysis
  const analysis = new ConstantPropagationAnalysis();
  const { results } = analysis.analyze(graph);
  
  // Track if any optimizations were applied
  let optimizationsApplied = false;
  
  // Apply the results to create an optimized program
  for (let i = 0; i < optimizedProgram.blocks.length; i++) {
    const block = optimizedProgram.blocks[i];
    if (!block) continue;
    
    const blockConstants = results.get(block.label) || new Map();
    
    // Replace variable uses with constants
    for (let j = 0; j < block.instructions.length; j++) {
      const instr = block.instructions[j];
      if (!instr) continue;
      
      if (instr.type === 'Assignment') {
        const optimizedValue = replaceConstants(instr.value, blockConstants);
        
        // If the optimized value is different from the original, mark the optimization
        if (JSON.stringify(optimizedValue) !== JSON.stringify(instr.value)) {
          block.instructions[j] = {
            ...instr,
            value: optimizedValue,
            optimized: true,
            originalValue: JSON.parse(JSON.stringify(instr.value))
          };
          optimizationsApplied = true;
        }
      }
    }
    
    // Optimize terminators
    if (block.terminator && block.terminator.condition) {
      const optimizedCondition = replaceConstants(block.terminator.condition, blockConstants);
      
      // If the condition is now a constant, we can simplify the branch
      const conditionChanged = JSON.stringify(optimizedCondition) !== JSON.stringify(block.terminator.condition);
      
      if (conditionChanged) {
        const originalCondition = JSON.parse(JSON.stringify(block.terminator.condition));
        
        if (optimizedCondition.type === 'BooleanLiteral' || 
            optimizedCondition.type === 'IntegerLiteral') {
          
          const isTrue = optimizedCondition.value !== 0 && optimizedCondition.value !== false;
          
          block.terminator = {
            ...block.terminator,
            condition: optimizedCondition,
            optimized: true,
            originalCondition: originalCondition,
            
            // For branch terminator, convert to jump if possible
            ...(block.terminator.type === 'Branch' ? {
              type: 'Jump',
              target: isTrue ? block.terminator.thenTarget : block.terminator.elseTarget
            } : {})
          };
        } else {
          block.terminator = {
            ...block.terminator,
            condition: optimizedCondition,
            optimized: true,
            originalCondition: originalCondition
          };
        }
        optimizationsApplied = true;
      }
    }
  }
  
  // Add metadata to indicate if optimizations were applied
  optimizedProgram.metadata = {
    ...optimizedProgram.metadata,
    constantPropagationApplied: optimizationsApplied
  };
  
  return optimizedProgram;
}

/**
 * Replace variables with known constant values
 * @param {object} expr - Expression to optimize
 * @param {Map} constants - Map of variable names to constant values
 * @returns {object} Optimized expression
 */
function replaceConstants(expr, constants) {
  if (!expr || !constants) return expr;
  
  if (expr.type === 'Variable') {
    const constVal = constants.get(expr.name);
    
    // If variable is a known constant, replace it
    if (constVal && constVal.state === Lattice.CONSTANT) {
      const type = typeof constVal.value === 'boolean' ? 'BooleanLiteral' : 'IntegerLiteral';
      return {
        type,
        value: constVal.value,
        originalVariable: expr.name
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
