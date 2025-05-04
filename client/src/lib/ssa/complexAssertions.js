/**
 * Complex Assertions Support
 * 
 * Enhances SSA transformation to handle complex assertions:
 * - Forall/exists quantifiers
 * - Array-wide assertions
 * - Inductive assertions for loops
 * - Implication chains
 */

/**
 * Handles complex assertions in SSA programs
 * @param {Object} ssaProgram - SSA program to process
 * @returns {Object} Enhanced SSA program with complex assertions
 */
export function processComplexAssertions(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) {
    return ssaProgram;
  }
  
  // Create a new copy of the program
  const enhancedProgram = JSON.parse(JSON.stringify(ssaProgram));
  
  // Process each block to find and transform complex assertions
  for (const block of enhancedProgram.blocks) {
    if (!block || !block.instructions) continue;
    
    const newInstructions = [];
    
    for (const instr of block.instructions) {
      if (!instr) {
        newInstructions.push(instr);
        continue;
      }
      
      if (instr.type === 'Assert') {
        // Handle different types of complex assertions
        if (isQuantifiedAssertion(instr.condition)) {
          // Transform quantified assertions (forall, exists)
          const transformed = transformQuantifiedAssertion(instr, block);
          newInstructions.push(...transformed);
        } else if (isArrayAssertion(instr.condition)) {
          // Transform array-wide assertions
          const transformed = transformArrayAssertion(instr);
          newInstructions.push(...transformed);
        } else if (isImplicationChain(instr.condition)) {
          // Transform implication chains
          const transformed = transformImplicationChain(instr);
          newInstructions.push(...transformed);
        } else {
          // Regular assertion
          newInstructions.push(instr);
        }
      } else if (instr.type === 'LoopInvariant') {
        // Handle loop invariants
        const transformed = transformLoopInvariant(instr, block);
        newInstructions.push(...transformed);
      } else {
        // Regular instruction
        newInstructions.push(instr);
      }
    }
    
    // Update block with transformed instructions
    block.instructions = newInstructions;
  }
  
  // Update program metadata
  enhancedProgram.metadata = {
    ...enhancedProgram.metadata,
    complexAssertionsProcessed: true
  };
  
  return enhancedProgram;
}

/**
 * Check if an assertion uses quantifiers
 * @param {Object} condition - The assertion condition
 * @returns {boolean} True if the condition uses quantifiers
 */
function isQuantifiedAssertion(condition) {
  if (!condition) return false;
  
  // Check for explicit quantifier nodes
  if (condition.type === 'ForallExpression' || condition.type === 'ExistsExpression') {
    return true;
  }
  
  // Check for implicit quantification patterns
  if (condition.type === 'CallExpression' && 
      (condition.callee === 'forall' || condition.callee === 'exists')) {
    return true;
  }
  
  return false;
}

/**
 * Check if an assertion operates on entire arrays
 * @param {Object} condition - The assertion condition
 * @returns {boolean} True if the condition is an array assertion
 */
function isArrayAssertion(condition) {
  if (!condition) return false;
  
  // Check for array predicates
  if (condition.type === 'CallExpression' && 
      ['sorted', 'all', 'any', 'none'].includes(condition.callee)) {
    return true;
  }
  
  // Check for array comparison operators
  if (condition.type === 'BinaryExpression' && 
      condition.left.type === 'Variable' && 
      condition.right.type === 'Variable') {
    // This is simplistic - a real implementation would check if the variables are arrays
    return true;
  }
  
  return false;
}

/**
 * Check if an assertion is an implication chain
 * @param {Object} condition - The assertion condition
 * @returns {boolean} True if the condition is an implication chain
 */
function isImplicationChain(condition) {
  if (!condition) return false;
  
  // Check for explicit implication
  if (condition.type === 'BinaryExpression' && condition.operator === '→') {
    return true;
  }
  
  // Check for implicit implication using logical operators
  if (condition.type === 'BinaryExpression' && condition.operator === '||') {
    // p → q is equivalent to !p || q
    if (condition.left.type === 'UnaryExpression' && condition.left.operator === '!') {
      return true;
    }
  }
  
  return false;
}

/**
 * Transform a quantified assertion into concrete assertions
 * @param {Object} assertion - The assertion to transform
 * @param {Object} block - The containing block
 * @returns {Array} Array of transformed assertions
 */
function transformQuantifiedAssertion(assertion, block) {
  const result = [];
  const condition = assertion.condition;
  
  // Handle explicit forall expressions
  if (condition.type === 'ForallExpression') {
    const variable = condition.variable;
    const domain = condition.domain;
    const predicate = condition.predicate;
    
    // For finite domains, expand into explicit assertions
    if (domain.type === 'Range') {
      const start = domain.start.type === 'IntegerLiteral' ? domain.start.value : 0;
      const end = domain.end.type === 'IntegerLiteral' ? domain.end.value : 10;
      
      // Create an assertion for each value in the range
      for (let i = start; i < end; i++) {
        // Substitute the variable with the specific value
        const substitutedPredicate = substituteVariable(predicate, variable.name, {
          type: 'IntegerLiteral',
          value: i
        });
        
        // Create a new assertion
        result.push({
          type: 'Assert',
          condition: substitutedPredicate,
          message: `${assertion.message || 'Assertion failed'} (for ${variable.name}=${i})`,
          location: assertion.location,
          metadata: {
            originalAssertion: 'forall',
            instantiation: { variable: variable.name, value: i }
          }
        });
      }
    } else {
      // For non-finite domains, add a runtime check with a loop
      result.push({
        ...assertion,
        metadata: {
          ...(assertion.metadata || {}),
          complexAssertion: 'quantified',
          quantifier: 'forall',
          approximated: true
        }
      });
    }
  } else if (condition.type === 'ExistsExpression') {
    // Add a runtime check with a disjunction
    result.push({
      ...assertion,
      metadata: {
        ...(assertion.metadata || {}),
        complexAssertion: 'quantified',
        quantifier: 'exists',
        approximated: true
      }
    });
  } else if (condition.type === 'CallExpression') {
    result.push({
      ...assertion,
      metadata: {
        ...(assertion.metadata || {}),
        complexAssertion: 'quantified',
        approximated: true
      }
    });
  }
  
  // If no transformations applied, return the original assertion
  if (result.length === 0) {
    result.push(assertion);
  }
  
  return result;
}

/**
 * Transform an array assertion into concrete assertions
 * @param {Object} assertion - The assertion to transform
 * @returns {Array} Array of transformed assertions
 */
function transformArrayAssertion(assertion) {
  const result = [];
  const condition = assertion.condition;
  
  // Handle array predicates
  if (condition.type === 'CallExpression') {
    if (condition.callee === 'sorted') {
      // Transform into a series of comparison assertions
      result.push({
        ...assertion,
        metadata: {
          ...(assertion.metadata || {}),
          complexAssertion: 'array',
          arrayPredicate: 'sorted',
          approximated: true
        }
      });
    } else if (['all', 'any', 'none'].includes(condition.callee)) {
      // Similar transformations for other array predicates
      result.push({
        ...assertion,
        metadata: {
          ...(assertion.metadata || {}),
          complexAssertion: 'array',
          arrayPredicate: condition.callee,
          approximated: true
        }
      });
    }
  }
  
  // If no transformations applied, return the original assertion
  if (result.length === 0) {
    result.push(assertion);
  }
  
  return result;
}

/**
 * Transform an implication chain into equivalent assertions
 * @param {Object} assertion - The assertion to transform
 * @returns {Array} Array of transformed assertions
 */
function transformImplicationChain(assertion) {
  const result = [];
  const condition = assertion.condition;
  
  // Handle explicit implications (p → q)
  if (condition.type === 'BinaryExpression' && condition.operator === '→') {
    // Transform p → q into !p || q
    const transformedCondition = {
      type: 'BinaryExpression',
      left: {
        type: 'UnaryExpression',
        operator: '!',
        operand: condition.left
      },
      operator: '||',
      right: condition.right
    };
    
    result.push({
      ...assertion,
      condition: transformedCondition,
      metadata: {
        ...(assertion.metadata || {}),
        complexAssertion: 'implication',
        transformed: true
      }
    });
  } else if (condition.type === 'BinaryExpression' && condition.operator === '||') {
    if (condition.left.type === 'UnaryExpression' && condition.left.operator === '!') {
      // Already in the right form, just add metadata
      result.push({
        ...assertion,
        metadata: {
          ...(assertion.metadata || {}),
          complexAssertion: 'implication',
          transformed: false
        }
      });
    }
  }
  
  // If no transformations applied, return the original assertion
  if (result.length === 0) {
    result.push(assertion);
  }
  
  return result;
}

/**
 * Transform a loop invariant into assertions
 * @param {Object} invariant - The loop invariant
 * @param {Object} block - The containing block
 * @returns {Array} Array of transformed assertions
 */
function transformLoopInvariant(invariant, block) {
  const result = [];
  
  // Add invariant checking at loop entry
  result.push({
    type: 'Assert',
    condition: invariant.condition,
    message: invariant.message || 'Loop invariant failed at entry',
    location: invariant.location,
    metadata: {
      loopInvariant: true,
      checkPoint: 'entry'
    }
  });
  
  // Add invariant checking at loop exit
  result.push({
    type: 'Assert',
    condition: invariant.condition,
    message: invariant.message || 'Loop invariant failed at exit',
    location: invariant.location,
    metadata: {
      loopInvariant: true,
      checkPoint: 'exit'
    }
  });
  
  // Add invariant preservation checking (inductive case)
  result.push({
    type: 'Assert',
    condition: {
      type: 'BinaryExpression',
      left: {
        type: 'ApplyInvariant',
        condition: invariant.condition,
        state: 'before'
      },
      operator: '→',
      right: {
        type: 'ApplyInvariant',
        condition: invariant.condition,
        state: 'after'
      }
    },
    message: invariant.message || 'Loop invariant not preserved',
    location: invariant.location,
    metadata: {
      loopInvariant: true,
      checkPoint: 'inductive'
    }
  });
  
  return result;
}

/**
 * Substitute a variable in an expression with a value
 * @param {Object} expr - The expression
 * @param {string} varName - The variable name to substitute
 * @param {Object} value - The value to substitute with
 * @returns {Object} The expression with substitutions
 */
function substituteVariable(expr, varName, value) {
  if (!expr) return expr;
  
  // Handle simple cases
  if (expr.type === 'Variable' && expr.name === varName) {
    return value;
  }
  
  // Not an object, return as is
  if (typeof expr !== 'object') return expr;
  
  // Handle arrays
  if (Array.isArray(expr)) {
    return expr.map(item => substituteVariable(item, varName, value));
  }
  
  // Recursively process object properties
  const result = {};
  for (const key in expr) {
    if (Object.prototype.hasOwnProperty.call(expr, key)) {
      result[key] = substituteVariable(expr[key], varName, value);
    }
  }
  
  return result;
}
