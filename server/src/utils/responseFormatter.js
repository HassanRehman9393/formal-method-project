/**
 * Formats a successful response
 * @param {Object} data - The data to send in the response
 * @returns {Object} Formatted response object
 */
exports.formatSuccessResponse = (data) => {
  return {
    success: true,
    data
  };
};

/**
 * Formats an error response
 * @param {String} message - Error message
 * @param {Number} statusCode - HTTP status code
 * @param {Object} details - Additional error details
 * @returns {Object} Formatted error object
 */
exports.formatErrorResponse = (message, statusCode = 500, details = null) => {
  const response = {
    success: false,
    error: message,
    statusCode
  };
  
  if (details) {
    response.details = details;
  }
  
  return response;
};

/**
 * Formats a verification result
 * @param {Boolean} verified - Whether assertions are verified
 * @param {Object} counterexample - Example inputs that violate assertions
 * @param {String} smtConstraints - Generated SMT constraints
 * @returns {Object} Formatted verification result
 */
exports.formatVerificationResult = (verified, counterexample = null, smtConstraints = null) => {
  return {
    verified,
    counterexample,
    smtConstraints
  };
};

/**
 * Formats an equivalence checking result
 * @param {Boolean} equivalent - Whether programs are equivalent
 * @param {Object} counterexample - Example inputs that show inequivalence
 * @param {String} smtConstraints - Generated SMT constraints
 * @returns {Object} Formatted equivalence result
 */
exports.formatEquivalenceResult = (equivalent, counterexample = null, smtConstraints = null) => {
  return {
    equivalent,
    counterexample,
    smtConstraints
  };
};
