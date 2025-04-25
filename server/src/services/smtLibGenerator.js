/**
 * SMT-LIB Format Generator
 * Utility functions to generate SMT-LIB format strings for different program constructs
 */

/**
 * Generate SMT-LIB format for variable declaration
 * @param {string} name - Variable name
 * @param {string} type - Variable type (Int, Bool, etc.)
 * @returns {string} SMT-LIB declaration
 */
function generateDeclaration(name, type = 'Int') {
  return `(declare-const ${name} ${type})`;
}

/**
 * Generate SMT-LIB format for variable assignment
 * @param {string} name - Variable name
 * @param {string|number|boolean} value - Value to assign
 * @returns {string} SMT-LIB assertion
 */
function generateAssignment(name, value) {
  const valueStr = typeof value === 'string' ? value : JSON.stringify(value);
  return `(assert (= ${name} ${valueStr}))`;
}

/**
 * Generate SMT-LIB format for arithmetic expression
 * @param {string} op - Operator (+, -, *, /, %, etc.)
 * @param {string|number} left - Left operand
 * @param {string|number} right - Right operand
 * @returns {string} SMT-LIB expression
 */
function generateArithmetic(op, left, right) {
  const leftStr = typeof left === 'string' ? left : JSON.stringify(left);
  const rightStr = typeof right === 'string' ? right : JSON.stringify(right);
  
  switch (op) {
    case '+': return `(+ ${leftStr} ${rightStr})`;
    case '-': return `(- ${leftStr} ${rightStr})`;
    case '*': return `(* ${leftStr} ${rightStr})`;
    case '/': return `(div ${leftStr} ${rightStr})`;
    case '%': return `(mod ${leftStr} ${rightStr})`;
    default: throw new Error(`Unsupported arithmetic operator: ${op}`);
  }
}

/**
 * Generate SMT-LIB format for comparison expression
 * @param {string} op - Operator (==, !=, <, <=, >, >=)
 * @param {string|number} left - Left operand
 * @param {string|number} right - Right operand
 * @returns {string} SMT-LIB expression
 */
function generateComparison(op, left, right) {
  const leftStr = typeof left === 'string' ? left : JSON.stringify(left);
  const rightStr = typeof right === 'string' ? right : JSON.stringify(right);
  
  switch (op) {
    case '==': return `(= ${leftStr} ${rightStr})`;
    case '!=': return `(not (= ${leftStr} ${rightStr}))`;
    case '<': return `(< ${leftStr} ${rightStr})`;
    case '<=': return `(<= ${leftStr} ${rightStr})`;
    case '>': return `(> ${leftStr} ${rightStr})`;
    case '>=': return `(>= ${leftStr} ${rightStr})`;
    default: throw new Error(`Unsupported comparison operator: ${op}`);
  }
}

/**
 * Generate SMT-LIB format for logical expression
 * @param {string} op - Operator (&&, ||)
 * @param {string} left - Left operand
 * @param {string} right - Right operand
 * @returns {string} SMT-LIB expression
 */
function generateLogical(op, left, right) {
  switch (op) {
    case '&&': return `(and ${left} ${right})`;
    case '||': return `(or ${left} ${right})`;
    default: throw new Error(`Unsupported logical operator: ${op}`);
  }
}

/**
 * Generate SMT-LIB format for logical negation
 * @param {string} expr - Expression to negate
 * @returns {string} SMT-LIB expression
 */
function generateNot(expr) {
  return `(not ${expr})`;
}

/**
 * Generate SMT-LIB format for assertion
 * @param {string} expr - Expression to assert
 * @returns {string} SMT-LIB assertion
 */
function generateAssertion(expr) {
  return `(assert ${expr})`;
}

/**
 * Generate SMT-LIB format for implication
 * @param {string} antecedent - Antecedent expression
 * @param {string} consequent - Consequent expression
 * @returns {string} SMT-LIB expression
 */
function generateImplication(antecedent, consequent) {
  return `(=> ${antecedent} ${consequent})`;
}

/**
 * Generate SMT-LIB format for ternary expression
 * @param {string} condition - Condition expression
 * @param {string} thenExpr - Then expression
 * @param {string} elseExpr - Else expression
 * @returns {string} SMT-LIB expression
 */
function generateITE(condition, thenExpr, elseExpr) {
  return `(ite ${condition} ${thenExpr} ${elseExpr})`;
}

/**
 * Generate SMT-LIB format for array declaration
 * @param {string} name - Array name
 * @param {string} indexType - Type of array indices (usually Int)
 * @param {string} valueType - Type of array values
 * @returns {string} SMT-LIB declaration for an array
 */
function generateArrayDeclaration(name, indexType = 'Int', valueType = 'Int') {
  return `(declare-const ${name} (Array ${indexType} ${valueType}))`;
}

/**
 * Generate SMT-LIB format for array select operation (reading array element)
 * @param {string} arrayName - Array name
 * @param {string|number} index - Array index
 * @returns {string} SMT-LIB select expression
 */
function generateArraySelect(arrayName, index) {
  const indexStr = typeof index === 'string' ? index : JSON.stringify(index);
  return `(select ${arrayName} ${indexStr})`;
}

/**
 * Generate SMT-LIB format for array store operation (writing array element)
 * @param {string} arrayName - Array name
 * @param {string|number} index - Array index
 * @param {string|number|boolean} value - Value to store
 * @returns {string} SMT-LIB store expression
 */
function generateArrayStore(arrayName, index, value) {
  const indexStr = typeof index === 'string' ? index : JSON.stringify(index);
  const valueStr = typeof value === 'string' ? value : JSON.stringify(value);
  return `(store ${arrayName} ${indexStr} ${valueStr})`;
}

/**
 * Generate SMT-LIB format for array assignment
 * @param {string} arrayName - Array name
 * @param {string|number} index - Array index
 * @param {string|number|boolean} value - Value to assign
 * @returns {string} SMT-LIB assertion for array update
 */
function generateArrayAssignment(arrayName, index, value) {
  return `(assert (= ${arrayName} ${generateArrayStore(arrayName, index, value)}))`;
}

/**
 * Generate SMT-LIB format for if-then-else expression
 * @param {string} condition - Condition expression
 * @param {string} thenExpr - Then expression
 * @param {string} elseExpr - Else expression
 * @returns {string} SMT-LIB if-then-else expression
 */
function generateITE(condition, thenExpr, elseExpr) {
  return `(ite ${condition} ${thenExpr} ${elseExpr})`;
}

/**
 * Generate SMT-LIB format for loop invariant assertion
 * @param {string} invariant - Invariant expression
 * @returns {string} SMT-LIB assertion for loop invariant
 */
function generateLoopInvariant(invariant) {
  return `(assert ${invariant})`;
}

/**
 * Generate SMT-LIB format for quantified expression
 * @param {string} quantifier - 'forall' or 'exists'
 * @param {Array} variables - Array of variable declarations [name, type]
 * @param {string} body - Body expression
 * @returns {string} SMT-LIB quantified expression
 */
function generateQuantifier(quantifier, variables, body) {
  const vars = variables.map(([name, type]) => `(${name} ${type})`).join(' ');
  return `(${quantifier} (${vars}) ${body})`;
}

/**
 * Generate SMT-LIB format for a loop unrolling step
 * @param {string} condition - Loop condition
 * @param {Array} bodyAssertions - Array of assertions in the loop body
 * @param {number} iteration - Current iteration number
 * @returns {Object} SMT-LIB assertions and declarations for this unrolling step
 */
function generateLoopUnrolling(condition, bodyAssertions, iteration) {
  const conditionVar = `loop_cond_${iteration}`;
  const declarations = [`(declare-const ${conditionVar} Bool)`];
  const assertions = [`(assert (= ${conditionVar} ${condition}))`];
  
  if (iteration > 0) {
    assertions.push(`(assert ${conditionVar})`);
    assertions.push(...bodyAssertions.map(assertion => `(assert ${assertion})`));
  }
  
  return { declarations, assertions, conditionVar };
}

/**
 * Generate a complete SMT-LIB script
 * @param {Array} declarations - Array of declarations
 * @param {Array} assertions - Array of assertions
 * @param {boolean} produceModels - Whether to produce models
 * @returns {string} Complete SMT-LIB script
 */
function generateScript(declarations, assertions, produceModels = true) {
  const header = [
    "(set-logic QF_LIA)", // Quantifier-Free Linear Integer Arithmetic
  ];
  
  if (produceModels) {
    header.push("(set-option :produce-models true)");
  }
  
  const checkSat = ["(check-sat)"];
  const getModel = produceModels ? ["(get-model)"] : [];
  
  return [
    ...header,
    ...declarations,
    ...assertions,
    ...checkSat,
    ...getModel
  ].join('\n');
}

module.exports = {
  generateDeclaration,
  generateAssignment,
  generateArithmetic,
  generateComparison,
  generateLogical,
  generateNot,
  generateAssertion,
  generateImplication,
  generateITE,
  generateArrayDeclaration,
  generateArraySelect,
  generateArrayStore,
  generateArrayAssignment,
  generateLoopInvariant,
  generateQuantifier,
  generateLoopUnrolling,
  generateScript
};
