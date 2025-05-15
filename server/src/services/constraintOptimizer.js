/**
 * Constraint Optimizer Service
 * Optimizes SMT constraints for better solver performance
 */

class ConstraintOptimizer {
  constructor() {
    console.log('[ConstraintOptimizer] Initialized');
  }
  
  /**
   * Simplify constraints to improve solver performance
   * @param {Object} constraints - The constraints to simplify
   * @returns {Object} Simplified constraints
   */
  simplifyConstraints(constraints) {
    console.log('[ConstraintOptimizer] Simplifying constraints');
    
    if (!constraints) return {};
    
    // Make a deep copy to avoid mutating the original
    const optimized = JSON.parse(JSON.stringify(constraints));
    
    // Perform simplifications on assertions
    if (optimized.assertions && Array.isArray(optimized.assertions)) {
      optimized.assertions = optimized.assertions.map(assertion => {
        if (typeof assertion === 'string') {
          return {
            constraint: this.simplifyConstraintString(assertion),
            description: 'Simplified constraint'
          };
        } else if (assertion.constraint) {
          return {
            ...assertion,
            constraint: this.simplifyConstraintString(assertion.constraint),
            description: assertion.description || 'Simplified constraint'
          };
        }
        return assertion;
      });
    }
    
    // If there's an SMT script, simplify it
    if (optimized.smtScript) {
      const lines = optimized.smtScript.split('\n');
      const simplifiedLines = lines.map(line => {
        // Only simplify assert lines
        if (line.trim().startsWith('(assert ')) {
          const assertContent = line.trim().substring(8, line.trim().length - 1);
          const simplified = this.simplifyConstraintString(assertContent);
          return `(assert ${simplified})`;
        }
        return line;
      });
      optimized.smtScript = simplifiedLines.join('\n');
    }
    
    return optimized;
  }
  
  /**
   * Optimize array-specific constraints
   * @param {Object} constraints - Constraints with array operations
   * @returns {Object} Optimized constraints
   */
  optimizeArrayConstraints(constraints) {
    console.log('[ConstraintOptimizer] Optimizing array constraints');
    
    if (!constraints) return constraints;
    
    // Deep copy
    const optimized = JSON.parse(JSON.stringify(constraints));
    
    // Optimize array access patterns in SMT script
    if (optimized.smtScript) {
      // Replace consecutive select operations for the same array with a single select
      // e.g., (select (select arr i) j) -> (select arr i j)
      optimized.smtScript = optimized.smtScript.replace(
        /\(select\s+\(select\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\)\s+([a-zA-Z0-9_]+)\)/g,
        '(select $1 $2 $3)'
      );
      
      // Optimize store-select patterns
      // e.g., (select (store arr i v) i) -> v
      optimized.smtScript = optimized.smtScript.replace(
        /\(select\s+\(store\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\)\s+\2\)/g,
        '$3'
      );
    }
    
    // Apply similar optimizations to individual assertions
    if (optimized.assertions && Array.isArray(optimized.assertions)) {
      optimized.assertions = optimized.assertions.map(assertion => {
        if (typeof assertion === 'string') {
          return this.optimizeArrayExpression(assertion);
        } else if (assertion.constraint) {
            return {
              ...assertion,
            constraint: this.optimizeArrayExpression(assertion.constraint)
          };
        }
        return assertion;
      });
    }
    
    return optimized;
  }
  
  /**
   * Optimize array expressions in constraints
   * @param {string} expression - SMT constraint expression
   * @returns {string} Optimized expression
   */
  optimizeArrayExpression(expression) {
    if (typeof expression !== 'string') return expression;
    
    // Replace consecutive select operations
    let optimized = expression.replace(
      /\(select\s+\(select\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\)\s+([a-zA-Z0-9_]+)\)/g,
      '(select $1 $2 $3)'
    );
    
    // Optimize store-select patterns
    optimized = optimized.replace(
      /\(select\s+\(store\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\)\s+\2\)/g,
      '$3'
    );
    
    return optimized;
  }
  
  /**
   * Simplify a single constraint string
   * @param {string} constraint - SMT constraint string
   * @returns {string} Simplified constraint
   */
  simplifyConstraintString(constraint) {
    if (!constraint || typeof constraint !== 'string') return constraint;
    
    // Simple constant folding - replace simple arithmetic expressions with their results
    let simplified = constraint;
    
    // Replace (+ X 0) with X
    simplified = simplified.replace(/\(\s*\+\s+([a-zA-Z0-9_]+)\s+0\s*\)/g, '$1');
    simplified = simplified.replace(/\(\s*\+\s+0\s+([a-zA-Z0-9_]+)\s*\)/g, '$1');
    
    // Replace (* X 1) with X
    simplified = simplified.replace(/\(\s*\*\s+([a-zA-Z0-9_]+)\s+1\s*\)/g, '$1');
    simplified = simplified.replace(/\(\s*\*\s+1\s+([a-zA-Z0-9_]+)\s*\)/g, '$1');
    
    // Replace (* X 0) with 0
    simplified = simplified.replace(/\(\s*\*\s+([a-zA-Z0-9_]+)\s+0\s*\)/g, '0');
    simplified = simplified.replace(/\(\s*\*\s+0\s+([a-zA-Z0-9_]+)\s*\)/g, '0');
    
    // Replace (- X 0) with X
    simplified = simplified.replace(/\(\s*\-\s+([a-zA-Z0-9_]+)\s+0\s*\)/g, '$1');
    
    // Replace (= X X) with true
    simplified = simplified.replace(/\(\s*=\s+([a-zA-Z0-9_]+)\s+\1\s*\)/g, 'true');
    
    // Replace (and X true) with X
    simplified = simplified.replace(/\(\s*and\s+([a-zA-Z0-9_]+)\s+true\s*\)/g, '$1');
    simplified = simplified.replace(/\(\s*and\s+true\s+([a-zA-Z0-9_]+)\s*\)/g, '$1');
    
    // Replace (or X false) with X
    simplified = simplified.replace(/\(\s*or\s+([a-zA-Z0-9_]+)\s+false\s*\)/g, '$1');
    simplified = simplified.replace(/\(\s*or\s+false\s+([a-zA-Z0-9_]+)\s*\)/g, '$1');
    
    // Replace (and X false) with false
    simplified = simplified.replace(/\(\s*and\s+([a-zA-Z0-9_]+)\s+false\s*\)/g, 'false');
    simplified = simplified.replace(/\(\s*and\s+false\s+([a-zA-Z0-9_]+)\s*\)/g, 'false');
    
    // Replace (or X true) with true
    simplified = simplified.replace(/\(\s*or\s+([a-zA-Z0-9_]+)\s+true\s*\)/g, 'true');
    simplified = simplified.replace(/\(\s*or\s+true\s+([a-zA-Z0-9_]+)\s*\)/g, 'true');
    
    return simplified;
  }
}

// Export singleton instance
module.exports = new ConstraintOptimizer(); 
