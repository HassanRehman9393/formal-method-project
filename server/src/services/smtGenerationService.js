/**
 * SMT Generation Service
 * Provides high-level API for generating SMT constraints from programs
 */
const smtGenerator = require('./smtGenerator');
const smtLibGenerator = require('./smtLibGenerator');
const z3Service = require('./z3Service');

class SMTGenerationService {
  /**
   * Generate SMT constraints from program AST
   * @param {Object} ast - AST of the program
   * @returns {Object} SMT constraints
   */
  generateConstraints(ast) {
    try {
      const smtScript = smtGenerator.generateSMT(ast);
      
      return {
        success: true,
        smtScript,
        declarations: smtGenerator.declarations,
        assertions: smtGenerator.assertions,
        variables: Array.from(smtGenerator.variables)
      };
    } catch (error) {
      console.error('Error generating SMT constraints:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Generate SMT constraints for variable declarations
   * @param {Array} variables - Array of variable objects with names and types
   * @returns {Array} SMT declarations
   */
  generateVariableDeclarations(variables) {
    return variables.map(variable => {
      const { name, type = 'Int' } = variable;
      return smtLibGenerator.generateDeclaration(name, type);
    });
  }

  /**
   * Generate SMT constraints for variable assignments
   * @param {Array} assignments - Array of assignment objects with names and values
   * @returns {Array} SMT assertions
   */
  generateAssignments(assignments) {
    return assignments.map(assignment => {
      const { name, value } = assignment;
      return smtLibGenerator.generateAssignment(name, value);
    });
  }

  /**
   * Generate SMT constraints for assertions
   * @param {Array} assertions - Array of assertion expressions
   * @returns {Array} SMT assertions
   */
  generateAssertions(assertions) {
    return assertions.map(assertion => {
      return smtLibGenerator.generateAssertion(assertion);
    });
  }

  /**
   * Generate a complete SMT-LIB script
   * @param {Object} program - Program representation with declarations, assignments, assertions
   * @returns {string} SMT-LIB script
   */
  generateSMTScript(program) {
    try {
      const declarations = this.generateVariableDeclarations(program.variables || []);
      const assignments = this.generateAssignments(program.assignments || []);
      const assertions = this.generateAssertions(program.assertions || []);
      
      return smtLibGenerator.generateScript(
        declarations, 
        [...assignments, ...assertions],
        true
      );
    } catch (error) {
      console.error('Error generating SMT script:', error);
      return `; Error generating SMT script: ${error.message}`;
    }
  }

  /**
   * Verify a program using SMT constraints
   * @param {Object} ast - AST of the program
   * @returns {Promise<Object>} Verification result
   */
  async verifyProgram(ast) {
    try {
      const constraints = this.generateConstraints(ast);
      
      if (!constraints.success) {
        return {
          success: false,
          error: constraints.error
        };
      }
      
      // We'll implement the full verification in Days 7-12
      // For now, just return the generated constraints
      return {
        success: true,
        smtScript: constraints.smtScript,
        declarations: constraints.declarations,
        assertions: constraints.assertions,
        variables: constraints.variables
      };
    } catch (error) {
      console.error('Error verifying program:', error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Generate SMT for simple examples (for testing purposes)
   * @returns {Object} Example SMT constraints
   */
  generateExamples() {
    const examples = {
      // Example 1: x = 5, y = x + 3, z = x + y, assert z > 10
      example1: {
        variables: [
          { name: 'x', type: 'Int' },
          { name: 'y', type: 'Int' },
          { name: 'z', type: 'Int' }
        ],
        assignments: [
          { name: 'x', value: 5 },
          { name: 'y', value: smtLibGenerator.generateArithmetic('+', 'x', 3) },
          { name: 'z', value: smtLibGenerator.generateArithmetic('+', 'x', 'y') }
        ],
        assertions: [
          smtLibGenerator.generateComparison('>', 'z', 10)
        ]
      },
      
      // Example 2: x = a, y = b, assert x != y
      example2: {
        variables: [
          { name: 'x', type: 'Int' },
          { name: 'y', type: 'Int' },
          { name: 'a', type: 'Int' },
          { name: 'b', type: 'Int' }
        ],
        assignments: [
          { name: 'x', value: 'a' },
          { name: 'y', value: 'b' }
        ],
        assertions: [
          smtLibGenerator.generateComparison('!=', 'x', 'y')
        ]
      },
      
      // Example 3: Boolean logic
      example3: {
        variables: [
          { name: 'p', type: 'Bool' },
          { name: 'q', type: 'Bool' },
          { name: 'r', type: 'Bool' }
        ],
        assignments: [
          { name: 'r', value: smtLibGenerator.generateLogical('&&', 'p', 'q') }
        ],
        assertions: [
          smtLibGenerator.generateImplication('r', 'p')
        ]
      }
    };
    
    // Generate SMT-LIB scripts for each example
    const scripts = {};
    for (const [name, example] of Object.entries(examples)) {
      scripts[name] = this.generateSMTScript(example);
    }
    
    return scripts;
  }
}

module.exports = new SMTGenerationService();
