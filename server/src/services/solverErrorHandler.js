/**
 * Solver Error Handler
 * Handles edge cases and errors in the Z3 solver integration
 */

/**
 * Solver error types
 */
const ErrorType = {
  TIMEOUT: 'TIMEOUT',
  MEMORY_LIMIT: 'MEMORY_LIMIT',
  SYNTAX_ERROR: 'SYNTAX_ERROR',
  INVALID_CONSTRAINT: 'INVALID_CONSTRAINT',
  UNSATISFIABLE: 'UNSATISFIABLE',
  UNKNOWN: 'UNKNOWN',
  SOLVER_CRASH: 'SOLVER_CRASH',
  CONNECTION_ERROR: 'CONNECTION_ERROR'
};

/**
 * Handle solver errors and classify them
 * @param {Error} error - The error object
 * @returns {Object} Classified error with recovery suggestions
 */
function handleSolverError(error) {
  const errorInfo = {
    originalError: error,
    type: ErrorType.UNKNOWN,
    message: error.message || 'Unknown solver error',
    recoverable: false,
    recoverySuggestion: null
  };
  
  if (!error) {
    return {
      ...errorInfo,
      message: 'Undefined error occurred'
    };
  }
  
  // Check for timeout errors
  if (error.message && error.message.includes('timeout')) {
    errorInfo.type = ErrorType.TIMEOUT;
    errorInfo.recoverable = true;
    errorInfo.recoverySuggestion = 'Increase timeout duration or simplify constraints';
  }
  // Check for memory limit errors
  else if (error.message && (error.message.includes('memory') || error.message.includes('out of memory'))) {
    errorInfo.type = ErrorType.MEMORY_LIMIT;
    errorInfo.recoverable = true;
    errorInfo.recoverySuggestion = 'Reduce constraint complexity or array sizes';
  }
  // Check for syntax errors in SMT-LIB
  else if (error.message && (error.message.includes('syntax') || error.message.includes('parse'))) {
    errorInfo.type = ErrorType.SYNTAX_ERROR;
    errorInfo.recoverable = false;
    errorInfo.recoverySuggestion = 'Check SMT-LIB constraint syntax';
  }
  // Check for invalid constraints
  else if (error.message && error.message.includes('invalid')) {
    errorInfo.type = ErrorType.INVALID_CONSTRAINT;
    errorInfo.recoverable = false;
    errorInfo.recoverySuggestion = 'Review constraint formulation';
  }
  // Check for unsatisfiable constraints
  else if (error.message && error.message.includes('unsat')) {
    errorInfo.type = ErrorType.UNSATISFIABLE;
    errorInfo.recoverable = false;
    errorInfo.recoverySuggestion = 'The constraints are contradictory; review preconditions';
  }
  // Check for solver crashes
  else if (error.message && error.message.includes('crash')) {
    errorInfo.type = ErrorType.SOLVER_CRASH;
    errorInfo.recoverable = false;
    errorInfo.recoverySuggestion = 'The solver crashed; try with simplified constraints';
  }
  // Check for connection errors
  else if (error.message && (error.message.includes('connection') || error.message.includes('network'))) {
    errorInfo.type = ErrorType.CONNECTION_ERROR;
    errorInfo.recoverable = true;
    errorInfo.recoverySuggestion = 'Check network connectivity and try again';
  }
  
  return errorInfo;
}

/**
 * Attempt to recover from a solver error
 * @param {Object} errorInfo - The classified error
 * @param {Object} context - Context information for recovery
 * @returns {Object} Recovery result
 */
function attemptRecovery(errorInfo, context = {}) {
  if (!errorInfo.recoverable) {
    return {
      success: false,
      message: 'Error is not recoverable',
      error: errorInfo
    };
  }
  
  switch (errorInfo.type) {
    case ErrorType.TIMEOUT:
      return recoverFromTimeout(errorInfo, context);
      
    case ErrorType.MEMORY_LIMIT:
      return recoverFromMemoryLimit(errorInfo, context);
      
    case ErrorType.CONNECTION_ERROR:
      return recoverFromConnectionError(errorInfo, context);
      
    default:
      return {
        success: false,
        message: 'No recovery strategy available for this error type',
        error: errorInfo
      };
  }
}

/**
 * Recover from a timeout error
 * @param {Object} errorInfo - The classified error
 * @param {Object} context - Context information
 * @returns {Object} Recovery result
 */
function recoverFromTimeout(errorInfo, context) {
  const { currentTimeout = 10000 } = context;
  
  // If we can increase the timeout, do so
  if (context.maxTimeout && currentTimeout < context.maxTimeout) {
    const newTimeout = Math.min(
      context.maxTimeout,
      currentTimeout * (context.timeoutMultiplier || 2)
    );
    
    return {
      success: true,
      message: `Increased timeout from ${currentTimeout}ms to ${newTimeout}ms`,
      recoveryAction: 'INCREASE_TIMEOUT',
      newSettings: {
        ...context,
        currentTimeout: newTimeout
      }
    };
  }
  
  // If we can simplify constraints, try that
  if (context.constraints && context.canSimplifyConstraints) {
    return {
      success: true,
      message: 'Attempting to simplify constraints due to timeout',
      recoveryAction: 'SIMPLIFY_CONSTRAINTS',
      newSettings: {
        ...context,
        forceSimplifyConstraints: true
      }
    };
  }
  
  // If we can't recover, report failure
  return {
    success: false,
    message: 'Max timeout reached, no further recovery possible',
    error: errorInfo
  };
}

/**
 * Recover from a memory limit error
 * @param {Object} errorInfo - The classified error
 * @param {Object} context - Context information
 * @returns {Object} Recovery result
 */
function recoverFromMemoryLimit(errorInfo, context) {
  // If we can simplify constraints, try that
  if (context.constraints && context.canSimplifyConstraints) {
    return {
      success: true,
      message: 'Attempting to simplify constraints due to memory limits',
      recoveryAction: 'SIMPLIFY_CONSTRAINTS',
      newSettings: {
        ...context,
        forceSimplifyConstraints: true,
        aggressiveSimplification: true
      }
    };
  }
  
  // If we can reduce array sizes, try that
  if (context.constraints && context.constraints.arrays && context.constraints.arrays.length > 0) {
    return {
      success: true,
      message: 'Attempting to optimize array constraints due to memory limits',
      recoveryAction: 'OPTIMIZE_ARRAYS',
      newSettings: {
        ...context,
        forceOptimizeArrays: true
      }
    };
  }
  
  // If we can't recover, report failure
  return {
    success: false,
    message: 'Memory limit reached, no further recovery possible',
    error: errorInfo
  };
}

/**
 * Recover from a connection error
 * @param {Object} errorInfo - The classified error
 * @param {Object} context - Context information
 * @returns {Object} Recovery result
 */
function recoverFromConnectionError(errorInfo, context) {
  const { retryCount = 0, maxRetries = 3 } = context;
  
  if (retryCount < maxRetries) {
    return {
      success: true,
      message: `Retrying connection (attempt ${retryCount + 1} of ${maxRetries})`,
      recoveryAction: 'RETRY_CONNECTION',
      newSettings: {
        ...context,
        retryCount: retryCount + 1
      }
    };
  }
  
  return {
    success: false,
    message: `Max retries (${maxRetries}) reached, no further recovery possible`,
    error: errorInfo
  };
}

/**
 * Check if the provided constraints have potential issues
 * @param {Object} constraints - The constraints to validate
 * @returns {Object} Validation result
 */
function validateConstraints(constraints) {
  const issues = [];
  
  if (!constraints) {
    issues.push('Constraints object is null or undefined');
    return { valid: false, issues };
  }
  
  if (!constraints.assertions || !Array.isArray(constraints.assertions)) {
    issues.push('Assertions array is missing or not an array');
    return { valid: false, issues };
  }
  
  if (constraints.assertions.length === 0) {
    issues.push('Assertions array is empty');
  }
  
  // Check for common issues in assertions
  for (let i = 0; i < constraints.assertions.length; i++) {
    const assertion = constraints.assertions[i];
    
    if (!assertion.constraint) {
      issues.push(`Assertion at index ${i} is missing constraint property`);
      continue;
    }
    
    // Check for syntax issues in SMT-LIB
    if (hasSmtLibSyntaxIssues(assertion.constraint)) {
      issues.push(`Assertion at index ${i} has SMT-LIB syntax issues: "${assertion.constraint}"`);
    }
    
    // Check for potential division by zero
    if (assertion.constraint.includes('(div ') || assertion.constraint.includes('(/ ')) {
      issues.push(`Assertion at index ${i} contains division which may cause divide-by-zero: "${assertion.constraint}"`);
    }
    
    // Check for potentially problematic quantifiers
    if (assertion.constraint.includes('(forall ') || assertion.constraint.includes('(exists ')) {
      issues.push(`Assertion at index ${i} contains quantifiers which may be expensive: "${assertion.constraint}"`);
    }
  }
  
  // Check array declarations
  if (constraints.arrays && Array.isArray(constraints.arrays)) {
    if (constraints.arrays.length > 100) {
      issues.push(`Large number of arrays (${constraints.arrays.length}) may cause performance issues`);
    }
  }
  
  return {
    valid: issues.length === 0,
    issues
  };
}

/**
 * Check for common SMT-LIB syntax issues
 * @param {string} constraint - The constraint to check
 * @returns {boolean} True if issues found
 */
function hasSmtLibSyntaxIssues(constraint) {
  if (typeof constraint !== 'string') {
    return true;
  }
  
  // Check for balanced parentheses
  let parenCount = 0;
  for (let i = 0; i < constraint.length; i++) {
    if (constraint[i] === '(') parenCount++;
    if (constraint[i] === ')') parenCount--;
    if (parenCount < 0) return true; // Unbalanced parentheses
  }
  if (parenCount !== 0) return true; // Unbalanced parentheses
  
  // Check for common operator misspellings
  const operators = ['and', 'or', 'not', 'implies', 'ite', '=', '<', '>', '<=', '>=', '+', '-', '*', 'div', 'mod'];
  const constraintParts = constraint.split(/\s+/);
  
  for (const part of constraintParts) {
    // Check for close misspellings of operators
    if (!operators.includes(part) && part.length >= 2) {
      for (const op of operators) {
        if (op.length >= 2 && levenshteinDistance(part, op) === 1) {
          return true; // Possible misspelled operator
        }
      }
    }
  }
  
  return false;
}

/**
 * Calculate Levenshtein distance between two strings
 * @param {string} a - First string
 * @param {string} b - Second string
 * @returns {number} Edit distance
 */
function levenshteinDistance(a, b) {
  if (a.length === 0) return b.length;
  if (b.length === 0) return a.length;
  
  const matrix = [];
  
  // Initialize matrix
  for (let i = 0; i <= b.length; i++) {
    matrix[i] = [i];
  }
  
  for (let j = 0; j <= a.length; j++) {
    matrix[0][j] = j;
  }
  
  // Fill in the matrix
  for (let i = 1; i <= b.length; i++) {
    for (let j = 1; j <= a.length; j++) {
      if (b.charAt(i - 1) === a.charAt(j - 1)) {
        matrix[i][j] = matrix[i - 1][j - 1];
      } else {
        matrix[i][j] = Math.min(
          matrix[i - 1][j - 1] + 1, // substitution
          matrix[i][j - 1] + 1,     // insertion
          matrix[i - 1][j] + 1      // deletion
        );
      }
    }
  }
  
  return matrix[b.length][a.length];
}

module.exports = {
  ErrorType,
  handleSolverError,
  attemptRecovery,
  validateConstraints
}; 