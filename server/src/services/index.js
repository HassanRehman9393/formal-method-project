/**
 * Services index
 * Exports all services for easy importing
 */

// First declare non-dependent services 
const parserService = require('./parserService');
const ssaService = require('./ssaService');
const Z3Service = require('./z3Service');
const constraintOptimizer = require('./constraintOptimizer');
const ssaToSmtTranslator = require('./ssaToSmtTranslator');
const solverErrorHandler = require('./solverErrorHandler');

// Declare classes that will be instantiated
const SMTGenerationService = require('./smtGenerationService');
const VerificationService = require('./verificationService');
const EquivalenceService = require('./equivalenceService');
const SolverService = require('./solverService');

// Create instances for services that are classes
const z3Service = new Z3Service();
const smtGenerationService = new SMTGenerationService();
const solverService = new SolverService();
const equivalenceService = new EquivalenceService();
const verificationService = new VerificationService({
  smtGenerationService,
  z3Service,
  ssaService,
  parserService,
  constraintOptimizer
});

module.exports = {
  parserService,
  verificationService,
  ssaService,
  smtGenerationService,
  z3Service,
  constraintOptimizer,
  ssaToSmtTranslator,
  equivalenceService,
  solverService,
  solverErrorHandler
}; 