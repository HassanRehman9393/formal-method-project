/**
 * Browser version of the parser
 * Pre-compiled grammar for use in the web application
 */

// Note: In a real implementation, we would compile the grammar into JavaScript
// during the build process and include it here directly

// This will be populated with the pre-compiled parser
let pegParser = null;

/**
 * Custom error class for parsing errors with enhanced information
 */
export class ParseError extends Error {
  constructor(message, location, source, expected, found) {
    super(message);
    this.name = 'ParseError';
    this.location = location;
    this.source = source;
    this.expected = expected;
    this.found = found;
    
    // Generate helpful context for the error
    if (location && source) {
      this.context = this.generateErrorContext();
    }
  }
  
  /**
   * Generate a user-friendly error context showing the error location in the source
   */
  generateErrorContext() {
    const lines = this.source.split('\n');
    const lineNum = this.location.start.line;
    const colNum = this.location.start.column;
    
    // Get the line with the error and a couple of lines before/after for context
    const contextLines = [];
    for (let i = Math.max(0, lineNum - 2); i < Math.min(lines.length, lineNum + 3); i++) {
      const isErrorLine = i + 1 === lineNum;
      const linePrefix = `${i + 1}: ${isErrorLine ? '> ' : '  '}`;
      contextLines.push(linePrefix + lines[i]);
      
      // Add pointer to the error position
      if (isErrorLine) {
        contextLines.push(' '.repeat(linePrefix.length + colNum - 1) + '^');
      }
    }
    
    return contextLines.join('\n');
  }
  
  /**
   * Get a formatted error message for display
   */
  getFormattedMessage() {
    let msg = `${this.name}: ${this.message}\n`;
    
    if (this.location) {
      msg += `at line ${this.location.start.line}, column ${this.location.start.column}\n`;
    }
    
    if (this.context) {
      msg += `\n${this.context}\n`;
    }
    
    return msg;
  }
}

/**
 * Initialize the parser
 */
export function initParser(precompiledParser) {
  if (precompiledParser) {
    pegParser = precompiledParser;
  } else {
    console.warn('No pre-compiled parser provided, parse method will throw an error');
    pegParser = {
      parse: () => {
        throw new Error('Parser not initialized with pre-compiled grammar');
      }
    };
  }
  return pegParser;
}

/**
 * Parse a program string into an AST
 * @param {string} input - Program source code
 * @returns {Object} Abstract Syntax Tree
 * @throws {ParseError} On syntax errors with location info
 */
export function parse(input) {
  if (!pegParser) {
    throw new Error('Parser not initialized. Call initParser first.');
  }
  
  try {
    return pegParser.parse(input);
  } catch (error) {
    // Convert PEG.js error to a more user-friendly format
    throw new ParseError(
      error.message,
      error.location,
      input,
      error.expected,
      error.found
    );
  }
}

/**
 * Validate an AST for semantic errors
 * @param {Object} ast - The AST to check
 * @returns {Array} Array of semantic errors, if any
 */
export function validateAst(ast) {
  const errors = [];
  const variables = new Set();
  
  // Simple visitor pattern to traverse the AST
  function visit(node, parent = null) {
    if (!node || typeof node !== 'object') return;
    
    // Add parent reference for context
    if (parent) {
      node.parent = parent;
    }
    
    // Check for undefined variable usage
    if (node.type === 'Identifier' && !variables.has(node.name)) {
      // Skip checking on left side of assignment (declaration)
      const isDeclaration = node.parent && 
                          node.parent.type === 'AssignmentStatement' && 
                          node.parent.target === node;
      if (!isDeclaration) {
        errors.push({
          message: `Undefined variable "${node.name}"`,
          location: node.location
        });
      }
    }
    
    // Track variable declarations
    if (node.type === 'AssignmentStatement' && 
        node.target.type === 'Identifier') {
      variables.add(node.target.name);
    }
    
    // Visit all properties of the node
    for (const prop in node) {
      if (node.hasOwnProperty(prop) && typeof node[prop] === 'object' && prop !== 'parent') {
        visit(node[prop], node);
      }
    }
  }
  
  visit(ast);
  return errors;
}

export default { 
  parse,
  ParseError,
  validateAst,
  initParser
};
