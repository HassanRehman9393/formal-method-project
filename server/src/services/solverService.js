/**
 * Solver Service
 * Handles interaction with SMT solvers to verify programs
 */
const z3Service = require('./z3Service');

class SolverService {
  constructor() {
    console.log('[SolverService] Service initialized');
  }

  /**
   * Verify SMT constraints using an SMT solver
   * 
   * @param {Object} smtConstraints - SMT constraints to verify
   * @param {Object} options - Verification options
   * @returns {Object} - Verification results
   */
  async verifySMT(smtConstraints, options = {}) {
    console.log('[SolverService] Verifying SMT constraints');
    
    try {
      const result = await z3Service.verifyAssertions(smtConstraints, options);
      
      return {
        sat: !result.verified, // If verified=true, then sat=false (meaning unsat)
        model: result.counterexample ? result.counterexample.inputs : null,
        trace: result.counterexample ? result.counterexample.trace : null,
        timedOut: result.timedOut || false,
        statistics: {
          time: result.executionTime || 0,
          memory: result.memoryUsage || 0
        },
        message: result.message || ''
      };
    } catch (error) {
      console.error('[SolverService] Error in Z3 verification:', error);
      throw error;
    }
  }

  /**
   * Check satisfiability of SMT constraints
   * 
   * @param {Object} smtConstraints - SMT constraints to check
   * @param {Object} options - Solver options
   * @returns {Object} - Results including satisfiability and model
   */
  async checkSat(smtConstraints, options = {}) {
    return this.verifySMT(smtConstraints, options);
  }
  
  /**
   * Check if two programs are equivalent
   * 
   * @param {Object} equivalenceConstraints - Constraints for equivalence checking
   * @param {Object} options - Verification options
   * @returns {Object} - Equivalence results
   */
  async checkEquivalence(equivalenceConstraints, options = {}) {
    console.log('[SolverService] Checking program equivalence');
    
    try {
      const result = await z3Service.checkEquivalence(equivalenceConstraints, options);
      
      return {
        equivalent: result.equivalent,
        sat: !result.equivalent, // If equivalent=true, then sat=false
        model: result.counterexample ? result.counterexample.inputs : null,
        trace: result.counterexample ? result.counterexample.trace : null,
        timedOut: result.timedOut || false,
        statistics: {
          time: result.executionTime || 0,
          memory: result.memoryUsage || 0
        },
        message: result.message || ''
      };
    } catch (error) {
      console.error('[SolverService] Error in equivalence checking:', error);
      throw error;
    }
  }
}

// Export a singleton instance
module.exports = new SolverService(); 