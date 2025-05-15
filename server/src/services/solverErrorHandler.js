/**
 * Solver Error Handler Service
 * Handles errors from the Z3 solver and provides recovery mechanisms
 */

// Error types
const ErrorType = {
  TIMEOUT: 'TIMEOUT',
  MEMORY_LIMIT: 'MEMORY_LIMIT',
  UNSUPPORTED_FEATURE: 'UNSUPPORTED_FEATURE',
  CONSTRAINT_ERROR: 'CONSTRAINT_ERROR',
  SYNTAX_ERROR: 'SYNTAX_ERROR',
  CONNECTION_ERROR: 'CONNECTION_ERROR',
  UNKNOWN_ERROR: 'UNKNOWN_ERROR'
};

class SolverErrorHandler {
  constructor() {
    console.log('[SolverErrorHandler] Initialized');
  }
  
  /**
   * Handle solver errors and determine the error type
   * @param {Error} error - The error thrown by the solver
   * @returns {Object} Error information
   */
  handleSolverError(error) {
    if (!error) {
      return {
        type: ErrorType.UNKNOWN_ERROR,
        message: 'Unknown error occurred',
        recoverySuggestion: 'Try simplifying the constraints or increasing the timeout'
      };
    }
    
    const errorMsg = error.message || error.toString();
    
    // Identify the error type
    if (errorMsg.includes('timeout') || errorMsg.includes('timed out')) {
      return {
        type: ErrorType.TIMEOUT,
        message: 'Solver exceeded the time limit',
        recoverySuggestion: 'Increase the timeout or simplify the constraints'
      };
    } else if (errorMsg.includes('memory') || errorMsg.includes('out of memory')) {
      return {
        type: ErrorType.MEMORY_LIMIT,
        message: 'Solver exceeded the memory limit',
        recoverySuggestion: 'Simplify the constraints or reduce the complexity'
      };
    } else if (errorMsg.includes('unsupported') || errorMsg.includes('not supported')) {
      return {
        type: ErrorType.UNSUPPORTED_FEATURE,
        message: 'The solver does not support this feature',
        recoverySuggestion: 'Modify the constraints to use supported features'
      };
    } else if (errorMsg.includes('syntax') || errorMsg.includes('parse')) {
      return {
        type: ErrorType.SYNTAX_ERROR,
        message: 'Syntax error in the constraints',
        recoverySuggestion: 'Check the syntax of the constraints'
      };
    } else if (errorMsg.includes('connection') || errorMsg.includes('network')) {
      return {
        type: ErrorType.CONNECTION_ERROR,
        message: 'Connection error with the solver',
        recoverySuggestion: 'Check the solver connection or restart the service'
      };
    } else if (errorMsg.includes('constraint') || errorMsg.includes('assertion')) {
      return {
        type: ErrorType.CONSTRAINT_ERROR,
        message: 'Error in constraint logic',
        recoverySuggestion: 'Check the logic of the constraints'
      };
    } else {
      return {
        type: ErrorType.UNKNOWN_ERROR,
        message: `Unknown error: ${errorMsg}`,
        recoverySuggestion: 'Try simplifying the constraints or check the solver configuration'
      };
    }
  }
  
  /**
   * Attempt to recover from a solver error
   * @param {Object} errorInfo - Error information
   * @param {Object} context - Recovery context
   * @returns {Object} Recovery result
   */
  attemptRecovery(errorInfo, context) {
    const { type, message } = errorInfo;
    const { 
      currentTimeout = 10000, 
      maxTimeout = 30000, 
      timeoutMultiplier = 2,
      canSimplifyConstraints = true,
      retryCount = 0,
      maxRetries = 3
    } = context;
    
    // Check if we've reached the maximum retry count
    if (retryCount >= maxRetries) {
      return {
        success: false,
        message: 'Maximum retry count reached',
        recoveryAction: 'NONE'
      };
    }
    
    // Handle specific error types
    switch (type) {
      case ErrorType.TIMEOUT:
        // Increase timeout if possible
        if (currentTimeout < maxTimeout) {
          const newTimeout = Math.min(currentTimeout * timeoutMultiplier, maxTimeout);
          return {
            success: true,
            message: `Increasing timeout from ${currentTimeout}ms to ${newTimeout}ms`,
            recoveryAction: 'INCREASE_TIMEOUT',
            newSettings: {
              timeout: newTimeout,
              retryCount: retryCount + 1
            }
          };
        }
        break;
        
      case ErrorType.MEMORY_LIMIT:
      case ErrorType.CONSTRAINT_ERROR:
        // Simplify constraints if possible
        if (canSimplifyConstraints) {
          return {
            success: true,
            message: 'Attempting to simplify constraints',
            recoveryAction: 'SIMPLIFY_CONSTRAINTS',
            newSettings: {
              retryCount: retryCount + 1
            }
          };
        }
        break;
        
      case ErrorType.CONNECTION_ERROR:
        // Retry the connection
        return {
          success: true,
          message: 'Retrying connection',
          recoveryAction: 'RETRY_CONNECTION',
          newSettings: {
            retryCount: retryCount + 1
          }
        };
        
      case ErrorType.UNSUPPORTED_FEATURE:
        // Try to optimize array constraints
        return {
          success: true,
          message: 'Attempting to optimize array operations',
          recoveryAction: 'OPTIMIZE_ARRAYS',
          newSettings: {
            retryCount: retryCount + 1
          }
        };
    }
    
    // No recovery action possible
    return {
      success: false,
      message: 'No recovery action possible',
      recoveryAction: 'NONE'
    };
  }
  
  /**
   * Validate constraints before sending to solver
   * @param {Object} constraints - Constraints to validate
   * @returns {Object} Validation result
   */
  validateConstraints(constraints) {
    if (!constraints) {
      return {
        valid: false,
        issues: ['Constraints object is null or undefined']
      };
    }
    
    const issues = [];
    
    // Check for empty constraints
    if (!constraints.declarations || constraints.declarations.length === 0) {
      issues.push('No variable declarations found');
    }
    
    if (!constraints.assertions || constraints.assertions.length === 0) {
      issues.push('No assertions found');
    }
    
    // Check for common SMT syntax issues in assertions
    if (constraints.assertions && Array.isArray(constraints.assertions)) {
      for (let i = 0; i < constraints.assertions.length; i++) {
        const assertion = constraints.assertions[i];
        const constraint = typeof assertion === 'string' 
          ? assertion 
          : (assertion.constraint || '');
        
        // Check for unbalanced parentheses
        const openCount = (constraint.match(/\(/g) || []).length;
        const closeCount = (constraint.match(/\)/g) || []).length;
        
        if (openCount !== closeCount) {
          issues.push(`Unbalanced parentheses in assertion ${i+1}: ${constraint}`);
        }
        
        // Check for empty assertions
        if (!constraint.trim()) {
          issues.push(`Empty assertion at index ${i}`);
        }
      }
    }
    
    return {
      valid: issues.length === 0,
      issues
    };
  }
}

// Export singleton instance and error types
module.exports = Object.assign(new SolverErrorHandler(), { ErrorType });
