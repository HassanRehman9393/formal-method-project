/**
 * Parser Service
 * Parses programs written in the custom mini-language
 */
const fs = require('fs').promises;
const path = require('path');
const util = require('util');

class ParserService {
  constructor() {
    this.parser = null;
    this.grammar = null;
    this.initialized = false;
    console.log('[ParserService] Service initialized');
  }
  
  /**
   * Initialize the parser
   * @returns {Promise<void>}
   */
  async initialize() {
    if (this.initialized) return;
    
    try {
      // In a real implementation, we would:
      // 1. Load the PEG.js grammar from a file
      // 2. Generate a parser using that grammar
      
      // For now, we'll create a simple placeholder parser
      this.initialized = true;
      console.log('[ParserService] Parser initialized successfully');
    } catch (error) {
      console.error('[ParserService] Failed to initialize parser:', error);
      throw error;
    }
  }
  
  /**
   * Parse a program string into an AST
   * @param {string} programCode - Program code in the custom language
   * @param {Object} options - Parsing options
   * @returns {Promise<Object>} Parsing result with AST or error
   */
  async parse(programCode, options = {}) {
    console.log('[ParserService] Parsing program:', programCode?.substring(0, 30) + '...');
    await this.initialize();
    
    try {
      // This is a placeholder for the actual parsing logic
      // In a real implementation, we would use the PEG.js parser
      
      if (!programCode || typeof programCode !== 'string') {
        throw new Error('Invalid program code');
      }
      
      // For demonstration, we'll do some very basic "parsing"
      const ast = this.mockParser(programCode);
      console.log('[ParserService] Parsing successful');
      
      return {
        success: true,
        ast
      };
    } catch (error) {
      console.error('[ParserService] Error parsing program:', error);
      return {
        success: false,
        error: error.message,
        location: error.location
      };
    }
  }
  
  /**
   * Validate program syntax
   * @param {string} programCode - Program code to validate
   * @returns {Promise<Object>} Validation result
   */
  async validate(programCode) {
    console.log('[ParserService] Validating program');
    try {
      const result = await this.parse(programCode);
      return {
        valid: result.success,
        error: result.error
      };
    } catch (error) {
      return {
        valid: false,
        error: error.message
      };
    }
  }
  
  /**
   * Generate a visualization of the AST
   * @param {Object} ast - Abstract Syntax Tree
   * @param {string} format - Output format (json, html, text)
   * @returns {string|Object} Visualization result
   */
  visualize(ast, format = 'json') {
    console.log('[ParserService] Visualizing AST in format:', format);
    if (!ast) {
      return format === 'json' ? {} : 'No AST provided';
    }
    
    if (format === 'json') {
      return ast;
    } else if (format === 'html') {
      return this.generateHtmlVisualization(ast);
    } else if (format === 'text') {
      return this.generateTextVisualization(ast);
    } else {
      return JSON.stringify(ast, null, 2);
    }
  }
  
  /**
   * Generate HTML visualization of AST
   * @param {Object} ast - Abstract Syntax Tree
   * @returns {string} HTML representation
   */
  generateHtmlVisualization(ast) {
    const jsonStr = JSON.stringify(ast, null, 2)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;');
    
    return `
      <!DOCTYPE html>
      <html>
        <head>
          <title>AST Visualization</title>
          <style>
            body { font-family: monospace; }
            pre { background: #f4f4f4; padding: 15px; border-radius: 4px; }
            .container { max-width: 1000px; margin: 0 auto; }
          </style>
        </head>
        <body>
          <div class="container">
            <h1>AST Visualization</h1>
            <pre>${jsonStr}</pre>
          </div>
        </body>
      </html>
    `;
  }
  
  /**
   * Generate text visualization of AST
   * @param {Object} ast - Abstract Syntax Tree
   * @returns {string} Text representation
   */
  generateTextVisualization(ast) {
    return util.inspect(ast, { depth: null, colors: false });
  }
  
  /**
   * Mock parser implementation for demonstration
   * @param {string} code - Program code
   * @returns {Object} Simple AST
   */
  mockParser(code) {
    const lines = code.split('\n').filter(line => line.trim());
    
    const program = {
      type: 'Program',
      body: []
    };
    
    // Very simple parsing for demonstration purposes
    for (const line of lines) {
      const trimmedLine = line.trim();
      
      // Skip comments
      if (trimmedLine.startsWith('//')) continue;
      
      // Variable assignment: x := 5;
      const assignMatch = trimmedLine.match(/(\w+)\s*:=\s*(.+?);/);
      if (assignMatch) {
        const [, name, valueStr] = assignMatch;
        program.body.push({
          type: 'VariableDeclaration',
          id: { type: 'Identifier', name },
          init: this.parseExpression(valueStr)
        });
        continue;
      }
      
      // Assert statement: assert(x > 5);
      const assertMatch = trimmedLine.match(/assert\s*\((.+?)\);/);
      if (assertMatch) {
        const [, condition] = assertMatch;
        program.body.push({
          type: 'AssertStatement',
          expression: this.parseExpression(condition)
        });
        continue;
      }
    }
    
    return program;
  }
  
  /**
   * Parse expression (very basic)
   * @param {string} expr - Expression string
   * @returns {Object} Expression AST node
   */
  parseExpression(expr) {
    // Number literal
    if (/^-?\d+(\.\d+)?$/.test(expr)) {
      const value = expr.includes('.') ? parseFloat(expr) : parseInt(expr, 10);
      return { type: 'Literal', value };
    }
    
    // Boolean literal
    if (expr === 'true' || expr === 'false') {
      return { type: 'Literal', value: expr === 'true' };
    }
    
    // Identifier
    if (/^\w+$/.test(expr)) {
      return { type: 'Identifier', name: expr };
    }
    
    // Very basic binary expression parsing
    const opMatch = expr.match(/(.+?)\s*([+\-*\/%<>=!&|]+)\s*(.+)/);
    if (opMatch) {
      const [, left, operator, right] = opMatch;
      return {
        type: 'BinaryExpression',
        operator,
        left: this.parseExpression(left.trim()),
        right: this.parseExpression(right.trim())
      };
    }
    
    // Default: just wrap as raw expression
    return { type: 'RawExpression', value: expr };
  }
}

// Create a singleton instance of the parser service
const parserService = new ParserService();
console.log('[ParserService] Singleton instance created');

// Export the service methods
module.exports = {
  /**
   * Parse a program into an AST
   * @param {string} program - Program code
   * @param {Object} options - Parsing options
   * @returns {Promise<Object>} Parsing result with AST
   */
  parseProgram: async (program, options) => {
    console.log('[ParserService] parseProgram called with program:', program?.substring(0, 30) + '...');
    
    if (!program) {
      console.error('[ParserService] No program provided');
      return {
        success: false,
        error: 'No program code provided'
      };
    }
    
    try {
      const result = await parserService.parse(program, options);
      console.log('[ParserService] Parse result success:', result.success);
      
      // Ensure we're returning a valid AST object even if parse didn't fully succeed
      if (!result.ast && result.success) {
        console.warn('[ParserService] Parse succeeded but no AST was returned, creating basic AST');
        // Create a minimal valid AST if none was returned
        result.ast = {
          type: 'Program',
          body: []
        };
      }
      
      return result;
    } catch (error) {
      console.error('[ParserService] Error in parseProgram:', error);
      return {
        success: false,
        error: `Parser error: ${error.message}`
      };
    }
  },
  
  /**
   * Validate program syntax
   * @param {string} program - Program code
   * @returns {Promise<Object>} Validation result
   */
  validateProgram: async (program) => {
    console.log('[ParserService] validateProgram called');
    return parserService.validate(program);
  },
  
  /**
   * Visualize an AST
   * @param {Object} ast - Abstract Syntax Tree
   * @param {string} format - Output format
   * @returns {string|Object} Visualization result
   */
  visualizeAST: (ast, format) => {
    console.log('[ParserService] visualizeAST called');
    return parserService.visualize(ast, format);
  }
};
