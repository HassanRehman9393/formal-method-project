/**
 * Constraint Optimizer Service
 * Provides functionality for simplifying and optimizing SMT constraints
 */

class ConstraintOptimizer {
  /**
   * Simplify constraints to improve solver performance
   * @param {Object} constraints - The SMT constraints to simplify
   * @returns {Object} Simplified constraints
   */
  simplifyConstraints(constraints) {
    if (!constraints || !constraints.assertions) {
      return constraints;
    }

    // Create a copy to avoid modifying the original
    const simplified = {
      ...constraints,
      assertions: [...constraints.assertions]
    };

    // Apply multiple simplification strategies
    this.removeRedundantConstraints(simplified);
    this.combineRelatedConstraints(simplified);
    this.simplifyExpressions(simplified);
    this.reorderConstraints(simplified);

    return simplified;
  }

  /**
   * Remove redundant constraints that don't affect the verification outcome
   * @param {Object} constraints - Constraints to optimize
   */
  removeRedundantConstraints(constraints) {
    if (!constraints.assertions) return;

    // Find and remove duplicate constraints
    const uniqueConstraints = new Set();
    constraints.assertions = constraints.assertions.filter(assertion => {
      if (!assertion.constraint) return true;
      
      // Skip if we've seen this exact constraint before
      if (uniqueConstraints.has(assertion.constraint)) {
        return false;
      }
      
      uniqueConstraints.add(assertion.constraint);
      return true;
    });
    
    // Remove tautologies (always true assertions)
    constraints.assertions = constraints.assertions.filter(assertion => {
      if (!assertion.constraint) return true;
      
      // Simple tautology detection (can be expanded)
      return !this.isTautology(assertion.constraint);
    });
  }

  /**
   * Check if a constraint is a tautology (always true)
   * @param {string} constraint - The constraint to check
   * @returns {boolean} Whether it's a tautology
   */
  isTautology(constraint) {
    // Simple tautology check - could be expanded
    const tautologies = [
      '(= x x)',
      '(>= x x)',
      '(<= x x)',
      '(or true false)',
      '(or true true)',
      '(and true true)',
      '(=> false true)'
    ];
    
    return tautologies.includes(constraint);
  }

  /**
   * Combine related constraints to reduce the number of constraints
   * @param {Object} constraints - Constraints to optimize
   */
  combineRelatedConstraints(constraints) {
    if (!constraints.assertions) return;
    
    // Group constraints by variable
    const variableGroups = this.groupConstraintsByVariable(constraints.assertions);
    
    // For each variable, try to combine range constraints
    // For example, (> x 5) and (< x 10) could become (and (> x 5) (< x 10))
    const newAssertions = [];
    const combinedIndices = new Set();
    
    for (const [variable, indices] of Object.entries(variableGroups)) {
      if (indices.length <= 1) {
        continue; // Nothing to combine
      }
      
      // Try to combine constraints for this variable
      const rangeConstraints = this.findRangeConstraints(constraints.assertions, indices, variable);
      
      if (rangeConstraints.length > 1) {
        // We have range constraints that can be combined
        const combinedConstraint = this.combineRangeConstraints(rangeConstraints, variable);
        if (combinedConstraint) {
          // Add the combined constraint
          newAssertions.push({
            constraint: combinedConstraint,
            isVerificationTarget: rangeConstraints.some(idx => 
              constraints.assertions[idx].isVerificationTarget
            ),
            description: `Combined range constraint for ${variable}`
          });
          
          // Mark these constraints as combined
          rangeConstraints.forEach(idx => combinedIndices.add(idx));
        }
      }
    }
    
    // Add combined constraints and keep non-combined ones
    constraints.assertions = [
      ...constraints.assertions.filter((_, i) => !combinedIndices.has(i)),
      ...newAssertions
    ];
  }

  /**
   * Group constraint indices by variable they constrain
   * @param {Array} assertions - List of assertions
   * @returns {Object} Map of variable names to assertion indices
   */
  groupConstraintsByVariable(assertions) {
    const variableGroups = {};
    
    assertions.forEach((assertion, index) => {
      if (!assertion.constraint) return;
      
      // Extract variables using a simple regex
      // This is a simplistic approach - a real implementation would use proper parsing
      const matches = assertion.constraint.match(/\b[a-zA-Z][a-zA-Z0-9_]*\b/g);
      
      if (matches) {
        // Skip common SMT-LIB keywords like and, or, true, false
        const keywords = ['and', 'or', 'not', 'true', 'false', 'ite', 'select', 'store'];
        const variables = matches.filter(m => !keywords.includes(m));
        
        // Add this assertion to groups for each variable
        variables.forEach(variable => {
          if (!variableGroups[variable]) {
            variableGroups[variable] = [];
          }
          variableGroups[variable].push(index);
        });
      }
    });
    
    return variableGroups;
  }

  /**
   * Find range constraints for a variable
   * @param {Array} assertions - List of assertions
   * @param {Array} indices - Indices of assertions to check
   * @param {string} variable - Variable to find ranges for
   * @returns {Array} Indices of range constraints
   */
  findRangeConstraints(assertions, indices, variable) {
    // Look for constraints like (< x N), (> x N), (<= x N), (>= x N)
    const rangeIndices = [];
    
    indices.forEach(idx => {
      const constraint = assertions[idx].constraint;
      if (constraint.match(new RegExp(`\\((<|<=|>|>=)\\s+${variable}\\s+\\d+\\)`)) ||
          constraint.match(new RegExp(`\\((<|<=|>|>=)\\s+\\d+\\s+${variable}\\)`))) {
        rangeIndices.push(idx);
      }
    });
    
    return rangeIndices;
  }

  /**
   * Combine range constraints for a variable
   * @param {Array} rangeIndices - Indices of range constraints
   * @param {string} variable - The variable name
   * @returns {string} Combined constraint
   */
  combineRangeConstraints(rangeIndices, variable) {
    // This is a simplified implementation - a real one would need proper parsing
    // For demo, we'll just combine with an "and"
    if (rangeIndices.length <= 1) {
      return null;
    }
    
    return `(and ${rangeIndices.map(idx => assertions[idx].constraint).join(' ')})`;
  }

  /**
   * Simplify individual constraint expressions
   * @param {Object} constraints - Constraints to optimize
   */
  simplifyExpressions(constraints) {
    if (!constraints.assertions) return;
    
    // Apply algebraic simplifications to individual constraints
    constraints.assertions = constraints.assertions.map(assertion => {
      if (!assertion.constraint) return assertion;
      
      return {
        ...assertion,
        constraint: this.simplifyExpression(assertion.constraint)
      };
    });
  }

  /**
   * Simplify a single expression using algebraic rules
   * @param {string} expression - Expression to simplify
   * @returns {string} Simplified expression
   */
  simplifyExpression(expression) {
    // Apply simple algebraic simplifications
    let simplified = expression;
    
    // Replace (+ x 0) with x
    simplified = simplified.replace(/\(\+\s+([a-zA-Z0-9_]+)\s+0\)/g, '$1');
    simplified = simplified.replace(/\(\+\s+0\s+([a-zA-Z0-9_]+)\)/g, '$1');
    
    // Replace (* x 1) with x
    simplified = simplified.replace(/\(\*\s+([a-zA-Z0-9_]+)\s+1\)/g, '$1');
    simplified = simplified.replace(/\(\*\s+1\s+([a-zA-Z0-9_]+)\)/g, '$1');
    
    // Replace (* x 0) with 0
    simplified = simplified.replace(/\(\*\s+[a-zA-Z0-9_]+\s+0\)/g, '0');
    simplified = simplified.replace(/\(\*\s+0\s+[a-zA-Z0-9_]+\)/g, '0');
    
    // Replace (and x true) with x
    simplified = simplified.replace(/\(and\s+([a-zA-Z0-9_]+)\s+true\)/g, '$1');
    simplified = simplified.replace(/\(and\s+true\s+([a-zA-Z0-9_]+)\)/g, '$1');
    
    // Replace (and x false) with false
    simplified = simplified.replace(/\(and\s+[a-zA-Z0-9_]+\s+false\)/g, 'false');
    simplified = simplified.replace(/\(and\s+false\s+[a-zA-Z0-9_]+\)/g, 'false');
    
    // Replace (or x false) with x
    simplified = simplified.replace(/\(or\s+([a-zA-Z0-9_]+)\s+false\)/g, '$1');
    simplified = simplified.replace(/\(or\s+false\s+([a-zA-Z0-9_]+)\)/g, '$1');
    
    // Replace (or x true) with true
    simplified = simplified.replace(/\(or\s+[a-zA-Z0-9_]+\s+true\)/g, 'true');
    simplified = simplified.replace(/\(or\s+true\s+[a-zA-Z0-9_]+\)/g, 'true');
    
    return simplified;
  }

  /**
   * Reorder constraints for more efficient solving
   * @param {Object} constraints - Constraints to reorder
   */
  reorderConstraints(constraints) {
    if (!constraints.assertions) return;
    
    // Sort by complexity (simpler constraints first)
    constraints.assertions.sort((a, b) => {
      // Skip undefined constraints
      if (!a.constraint) return -1;
      if (!b.constraint) return 1;
      
      // Simple heuristic: shorter constraints are simpler
      return a.constraint.length - b.constraint.length;
    });
    
    // Move verification targets to the end (after context is established)
    const verificationTargets = constraints.assertions.filter(a => a.isVerificationTarget);
    const context = constraints.assertions.filter(a => !a.isVerificationTarget);
    
    constraints.assertions = [...context, ...verificationTargets];
  }

  /**
   * Optimize array constraints for better performance
   * @param {Object} constraints - Constraints to optimize
   * @returns {Object} Optimized constraints
   */
  optimizeArrayConstraints(constraints) {
    if (!constraints || !constraints.assertions) {
      return constraints;
    }

    // Create a copy to avoid modifying the original
    const optimized = {
      ...constraints,
      assertions: [...constraints.assertions]
    };

    // Apply array-specific optimizations
    this.localizeArrayAccesses(optimized);
    this.mergeArrayStores(optimized);
    this.eliminateUnusedArrayElements(optimized);

    return optimized;
  }

  /**
   * Localize array accesses to improve SMT solver performance
   * @param {Object} constraints - Constraints to optimize
   */
  localizeArrayAccesses(constraints) {
    if (!constraints.arrays || !constraints.assertions) return;
    
    // Find all array accesses and group them by array and index
    const arrayAccesses = this.findArrayAccesses(constraints.assertions);
    
    // Create local variables for frequently accessed elements
    let nextVarId = 1;
    const newAssertions = [];
    
    for (const [array, indices] of Object.entries(arrayAccesses)) {
      for (const [index, accessCount] of Object.entries(indices)) {
        // Only create locals for frequently accessed elements (>=2 times)
        if (accessCount >= 2) {
          const localVar = `${array}_${index}_local`;
          
          // Add an assertion to define the local variable
          newAssertions.push({
            constraint: `(= ${localVar} (select ${array} ${index}))`,
            isVerificationTarget: false,
            description: `Local variable for ${array}[${index}]`
          });
          
          // Replace array accesses with the local variable
          constraints.assertions = constraints.assertions.map(assertion => {
            if (!assertion.constraint) return assertion;
            
            // Replace (select array index) with localVar
            const pattern = new RegExp(`\\(select\\s+${array}\\s+${index}\\)`, 'g');
            const newConstraint = assertion.constraint.replace(pattern, localVar);
            
            return {
              ...assertion,
              constraint: newConstraint
            };
          });
        }
      }
    }
    
    // Add the new local variable definitions
    constraints.assertions = [...newAssertions, ...constraints.assertions];
  }

  /**
   * Find all array accesses in the constraints
   * @param {Array} assertions - Assertions to search
   * @returns {Object} Map of array names to indices and access counts
   */
  findArrayAccesses(assertions) {
    const arrayAccesses = {};
    
    assertions.forEach(assertion => {
      if (!assertion.constraint) return;
      
      // Find all (select array index) patterns
      const selectPattern = /\(select\s+([a-zA-Z][a-zA-Z0-9_]*)\s+(\d+|[a-zA-Z][a-zA-Z0-9_]*)\)/g;
      let match;
      
      while ((match = selectPattern.exec(assertion.constraint)) !== null) {
        const array = match[1];
        const index = match[2];
        
        if (!arrayAccesses[array]) {
          arrayAccesses[array] = {};
        }
        
        if (!arrayAccesses[array][index]) {
          arrayAccesses[array][index] = 0;
        }
        
        arrayAccesses[array][index]++;
      }
    });
    
    return arrayAccesses;
  }

  /**
   * Merge consecutive array store operations
   * @param {Object} constraints - Constraints to optimize
   */
  mergeArrayStores(constraints) {
    if (!constraints.assertions) return;
    
    // Find store operations
    const storeOps = [];
    constraints.assertions.forEach((assertion, index) => {
      if (!assertion.constraint) return;
      
      // Look for (= arr (store ...)) patterns
      if (assertion.constraint.match(/\(=\s+([a-zA-Z][a-zA-Z0-9_]*)\s+\(store\s+/)) {
        storeOps.push(index);
      }
    });
    
    // Merge consecutive stores to the same array
    // This is a complex operation that requires careful parsing and tracking
    // of array versions - simplified for this example
    
    // For simple cases, we can merge stores at different indices
    const mergeableGroups = this.findMergeableStoreGroups(constraints.assertions, storeOps);
    
    // Apply merges (omitted in this simplified version)
    // A full implementation would replace multiple store operations with one combined operation
  }

  /**
   * Find groups of mergeable array store operations
   * @param {Array} assertions - List of assertions
   * @param {Array} storeIndices - Indices of store operations
   * @returns {Array} Groups of mergeable operations
   */
  findMergeableStoreGroups(assertions, storeIndices) {
    // This implementation is simplified - a real implementation would
    // need to track array versions and dependencies between operations
    const arrayGroups = {};
    
    storeIndices.forEach(idx => {
      const assertion = assertions[idx];
      
      // Extract array name using regex
      const match = assertion.constraint.match(/\(=\s+([a-zA-Z][a-zA-Z0-9_]*)\s+\(store/);
      if (match) {
        const array = match[1];
        if (!arrayGroups[array]) {
          arrayGroups[array] = [];
        }
        arrayGroups[array].push(idx);
      }
    });
    
    return Object.values(arrayGroups).filter(group => group.length > 1);
  }

  /**
   * Eliminate unused array elements
   * @param {Object} constraints - Constraints to optimize
   */
  eliminateUnusedArrayElements(constraints) {
    if (!constraints.arrays || !constraints.assertions) return;
    
    // Find all accessed array indices
    const arrayAccesses = this.findArrayAccesses(constraints.assertions);
    
    // For each array, create a constraint that only defines the accessed elements
    // and ignore the rest
    
    // This optimization requires careful handling of quantifiers and is complex
    // to implement fully. In this simplified example, we'll just track the accesses.
    
    // Add metadata about accessed indices to help the solver
    constraints.arrayMetadata = constraints.arrayMetadata || {};
    
    for (const [array, indices] of Object.entries(arrayAccesses)) {
      constraints.arrayMetadata[array] = {
        accessedIndices: Object.keys(indices),
        accessCount: Object.values(indices).reduce((a, b) => a + b, 0)
      };
    }
  }
}

module.exports = new ConstraintOptimizer(); 