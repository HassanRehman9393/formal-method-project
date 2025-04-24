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
  generateScript
};
