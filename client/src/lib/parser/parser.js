/**
 * Parser module for the mini-language
 * Uses PEG.js to generate a parser from our grammar
 */

import pegjs from 'pegjs';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import * as astNodes from './ast-nodes.js';

// Get the directory name in ESM
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Read the grammar file
const grammarPath = path.join(__dirname, 'grammar.pegjs');
const grammar = fs.readFileSync(grammarPath, 'utf8');

// Generate the parser with error recovery options
const pegParser = pegjs.generate(grammar, {
  trace: false,
  // Enable cache to speed up parsing
  cache: true,
  // Error recovery isn't fully supported in PEG.js, but we can handle errors gracefully
  allowedStartRules: ['Program'],
});

/**
 * Parse a program string into an AST
 * @param {string} input - Program source code
 * @returns {Object} Abstract Syntax Tree
 * @throws {ParseError} On syntax errors with location info
 */
export function parse(input) {
  try {
    return pegParser.parse(input);
  } catch (error) {
    // Convert PEG.js error to a more user-friendly format
    const parseError = new ParseError(
      error.message,
      error.location,
      input,
      error.expected,
      error.found
    );
    throw parseError;
  }
}

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
    
    if (this.expected && this.expected.length > 0) {
      const expectedList = this.expected.map(e => e.description || e.type || e.text || 'unknown').join(', ');
      msg += `\nExpected one of: ${expectedList}\n`;
    }
    
    if (this.found !== null) {
      msg += `\nFound: "${this.found}"\n`;
    }
    
    return msg;
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
  function visit(node) {
    if (!node || typeof node !== 'object') return;
    
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
      if (node.hasOwnProperty(prop) && typeof node[prop] === 'object') {
        // Set parent reference for context
        if (node[prop] && typeof node[prop] === 'object') {
          node[prop].parent = node;
        }
        visit(node[prop]);
      }
    }
  }
  
  visit(ast);
  return errors;
}

export default { 
  parse,
  ParseError,
  validateAst
};
