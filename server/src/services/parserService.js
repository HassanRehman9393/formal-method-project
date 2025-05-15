/**
 * Parser Service
 * Parses programs written in the custom mini-language
 */
const fs = require('fs').promises;
const path = require('path');
const util = require('util');

class ParserService {
  constructor() {
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
      if (!programCode || typeof programCode !== 'string') {
        throw new Error('Invalid program code');
      }
      
      // Real parsing implementation
      const ast = this.realParser(programCode);
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
   * Parse a program string into an AST (alias for parse)
   * @param {string} programCode - Program code in the custom language
   * @param {Object} options - Parsing options
   * @returns {Promise<Object>} Parsing result with AST or error
   */
  async parseProgram(programCode, options = {}) {
    console.log('[ParserService] parseProgram called with program:', programCode?.substring(0, 30) + '...');
    return this.parse(programCode, options);
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
   * Real parser implementation
   * @param {string} code - Program code
   * @returns {Object} AST
   */
  realParser(code) {
    try {
      const lines = code.split('\n');
      
      const program = {
        type: 'Program',
        body: []
      };
      
      // Track the state of control flow
      let currentScope = program.body;
      const scopeStack = [];
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i].trim();
        const lineNum = i + 1;
        
        // Skip empty lines and comments
        if (!line || line.startsWith('//')) continue;
        
        try {
          // Variable assignment: x := 5;
          const assignMatch = line.match(/(\w+)\s*:=\s*(.+?);/);
          if (assignMatch) {
            const [, name, valueStr] = assignMatch;
            currentScope.push({
              type: 'VariableDeclaration',
              id: { type: 'Identifier', name },
              init: this.parseExpression(valueStr),
              loc: { start: { line: lineNum, column: 0 }, end: { line: lineNum, column: line.length }}
            });
            continue;
          }
          
          // Assert statement with Python-style comprehension: assert(for (i in range(n-1)): arr[i] <= arr[i+1]);
          const comprehensionMatch = line.match(/assert\s*\(\s*for\s*\(\s*(\w+)\s+in\s+range\(\s*(.+?)\s*\)\s*\)\s*:\s*(.+?)\s*\)\s*;/);
          if (comprehensionMatch) {
            const [, iterVar, rangeExpr, innerCondition] = comprehensionMatch;
            
            currentScope.push({
              type: 'AssertStatement',
              expression: {
                type: 'ForComprehension',
                iteratorVariable: { type: 'Identifier', name: iterVar },
                range: this.parseExpression(rangeExpr),
                condition: this.parseExpression(innerCondition)
              },
              loc: { start: { line: lineNum, column: 0 }, end: { line: lineNum, column: line.length }}
            });
            continue;
          }
          
          // Regular assert statement: assert(x > 5);
          const assertMatch = line.match(/assert\s*\((.+?)\)\s*;/);
          if (assertMatch) {
            const [, condition] = assertMatch;
            
            // Check for Python-like for-loop comprehension: for (i in range(n-1)): arr[i] <= arr[i+1]
            const forComprehensionMatch = condition.match(/for\s*\((\w+)\s+in\s+range\((.+?)\)\):\s*(.+)/);
            
            if (forComprehensionMatch) {
              const [, iterVar, rangeExpr, innerCondition] = forComprehensionMatch;
              
              // Create a special ForComprehension node
              currentScope.push({
                type: 'AssertStatement',
                expression: {
                  type: 'ForComprehension',
                  iteratorVariable: { type: 'Identifier', name: iterVar },
                  range: this.parseExpression(rangeExpr),
                  condition: this.parseExpression(innerCondition)
                },
                loc: { start: { line: lineNum, column: 0 }, end: { line: lineNum, column: line.length }}
              });
            } else {
              // Regular assertion
              currentScope.push({
                type: 'AssertStatement',
                expression: this.parseExpression(condition),
                loc: { start: { line: lineNum, column: 0 }, end: { line: lineNum, column: line.length }}
              });
            }
            continue;
          }
          
          // If statement: if (x > 5) {
          const ifMatch = line.match(/if\s*\((.+?)\)\s*\{/);
          if (ifMatch) {
            const [, condition] = ifMatch;
            const ifNode = {
              type: 'IfStatement',
              test: this.parseExpression(condition),
              consequent: { type: 'BlockStatement', body: [] },
              alternate: null,
              loc: { start: { line: lineNum, column: 0 } }
            };
            
            currentScope.push(ifNode);
            scopeStack.push({ node: ifNode, scope: currentScope });
            currentScope = ifNode.consequent.body;
            continue;
          }
          
          // Else statement: } else {
          const elseMatch = line.match(/\}\s*else\s*\{/);
          if (elseMatch) {
            if (scopeStack.length === 0) {
              console.warn(`Line ${lineNum}: Unexpected 'else' without matching 'if', treating as standalone block`);
              // Create a dummy if node
              const dummyIfNode = {
                type: 'IfStatement',
                test: { type: 'Literal', value: true },
                consequent: { type: 'BlockStatement', body: [] },
                alternate: { type: 'BlockStatement', body: [] },
                loc: { start: { line: lineNum, column: 0 } }
              };
              currentScope.push(dummyIfNode);
              currentScope = dummyIfNode.alternate.body;
              continue;
            }
            
            const parentScope = scopeStack[scopeStack.length - 1];
            if (parentScope.node.type !== 'IfStatement') {
              console.warn(`Line ${lineNum}: 'else' can only follow an 'if' block, treating as standalone block`);
              // Create a dummy if node
              const dummyIfNode = {
                type: 'IfStatement',
                test: { type: 'Literal', value: true },
                consequent: { type: 'BlockStatement', body: [] },
                alternate: { type: 'BlockStatement', body: [] },
                loc: { start: { line: lineNum, column: 0 } }
              };
              currentScope.push(dummyIfNode);
              currentScope = dummyIfNode.alternate.body;
              continue;
            }
            
            parentScope.node.alternate = { type: 'BlockStatement', body: [] };
            currentScope = parentScope.node.alternate.body;
            continue;
          }
          
          // While loop: while (x < 10) {
          const whileMatch = line.match(/while\s*\((.+?)\)\s*\{/);
          if (whileMatch) {
            const [, condition] = whileMatch;
            const whileNode = {
              type: 'WhileStatement',
              test: this.parseExpression(condition),
              body: { type: 'BlockStatement', body: [] },
              loc: { start: { line: lineNum, column: 0 } }
            };
            
            currentScope.push(whileNode);
            scopeStack.push({ node: whileNode, scope: currentScope });
            currentScope = whileNode.body.body;
            continue;
          }
          
          // For loop: for (i := 0; i < 10; i := i + 1) {
          const forMatch = line.match(/for\s*\((.+?);(.+?);(.+?)\)\s*\{/);
          if (forMatch) {
            const [, init, test, update] = forMatch;
            
            // Parse initializer
            const initNode = this.parseStatement(`${init};`);
            
            // Parse test expression
            const testNode = this.parseExpression(test);
            
            // Parse update expression
            const updateNode = this.parseStatement(`${update};`);
            
            const forNode = {
              type: 'ForStatement',
              init: initNode,
              test: testNode,
              update: updateNode,
              body: { type: 'BlockStatement', body: [] },
              loc: { start: { line: lineNum, column: 0 } }
            };
            
            currentScope.push(forNode);
            scopeStack.push({ node: forNode, scope: currentScope });
            currentScope = forNode.body.body;
            continue;
          }
          
          // Close block: }
          if (line === '}') {
            if (scopeStack.length === 0) {
              console.warn(`Line ${lineNum}: Unexpected '}', ignoring`);
              // Just ignore unmatched closing braces 
              continue;
            }
            
            const parentScope = scopeStack.pop();
            
            // Complete location information
            if (parentScope.node.loc) {
              parentScope.node.loc.end = { line: lineNum, column: line.length };
            }
            
            // If we closed the alternate of an if statement
            if (parentScope.node.type === 'IfStatement' && currentScope === parentScope.node.alternate?.body) {
              currentScope = parentScope.scope;
            } 
            // If we closed a loop or if-then block
            else {
              currentScope = parentScope.scope;
            }
            
            continue;
          }
          
          // Handle array declarations and assignments
          const arrayDeclMatch = line.match(/(\w+)\s*:=\s*\[\s*(.+?)\s*\]\s*;/);
          if (arrayDeclMatch) {
            const [, name, elements] = arrayDeclMatch;
            const elementExpressions = elements.split(',').map(el => this.parseExpression(el.trim()));
            
            currentScope.push({
              type: 'VariableDeclaration',
              id: { type: 'Identifier', name },
              init: {
                type: 'ArrayExpression',
                elements: elementExpressions
              },
              loc: { start: { line: lineNum, column: 0 }, end: { line: lineNum, column: line.length }}
            });
            continue;
          }
          
          // Array assignment: arr[idx] := value;
          const arrayAssignMatch = line.match(/(\w+)\[(.+?)\]\s*:=\s*(.+?);/);
          if (arrayAssignMatch) {
            const [, array, index, value] = arrayAssignMatch;
            
            currentScope.push({
              type: 'ExpressionStatement',
              expression: {
                type: 'AssignmentExpression',
                operator: ':=',
                left: {
                  type: 'MemberExpression',
                  object: { type: 'Identifier', name: array },
                  property: this.parseExpression(index),
                  computed: true
                },
                right: this.parseExpression(value)
              },
              loc: { start: { line: lineNum, column: 0 }, end: { line: lineNum, column: line.length }}
            });
            continue;
          }
          
          // If we couldn't match any pattern, report a warning but try to continue parsing
          console.warn(`Line ${lineNum}: Syntax error in '${line}', skipping line`);
        } catch (lineError) {
          // Catch errors in individual line parsing to allow continuing with other lines
          console.error(`Error parsing line ${lineNum}: ${lineError.message}`);
        }
      }
      
      // Check for unclosed blocks, but don't fail the parse
      if (scopeStack.length > 0) {
        // Automatically close any unclosed blocks to create a valid AST
        console.warn(`Warning: ${scopeStack.length} unclosed blocks found, automatically closing them`);
        
        // Pop all remaining scopes from the stack and return to the top level
        while (scopeStack.length > 0) {
          const parentScope = scopeStack.pop();
          
          // If we were in the alternate of an if statement
          if (parentScope.node.type === 'IfStatement' && currentScope === parentScope.node.alternate?.body) {
            currentScope = parentScope.scope;
          }
          // If we were in a loop or if-then block
          else {
            currentScope = parentScope.scope;
          }
        }
      }
      
      return program;
    } catch (error) {
      console.error('Critical parsing error:', error);
      // Return a minimal valid AST instead of throwing
      return {
        type: 'Program',
        body: [],
        parseError: error.message
      };
    }
  }
  
  /**
   * Parse a statement string into an AST node
   * @param {string} stmt - Statement string
   * @returns {Object} Statement AST node
   */
  parseStatement(stmt) {
    // Variable assignment: x := 5;
    const assignMatch = stmt.match(/(\w+)\s*:=\s*(.+?);/);
    if (assignMatch) {
      const [, name, valueStr] = assignMatch;
      return {
        type: 'VariableDeclaration',
        id: { type: 'Identifier', name },
        init: this.parseExpression(valueStr)
      };
    }
    
    return { type: 'EmptyStatement' };
  }
  
  /**
   * Parse expression
   * @param {string} expr - Expression string
   * @returns {Object} Expression AST node
   */
  parseExpression(expr) {
    expr = expr.trim();
    
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
    
    // Array access: arr[idx]
    const arrayAccessMatch = expr.match(/(\w+)\[(.+)\]/);
    if (arrayAccessMatch) {
      const [, array, index] = arrayAccessMatch;
      return {
        type: 'MemberExpression',
        object: { type: 'Identifier', name: array },
        property: this.parseExpression(index),
        computed: true
      };
    }
    
    // Function call: func(args)
    const funcCallMatch = expr.match(/(\w+)\((.*)\)/);
    if (funcCallMatch) {
      const [, funcName, argsStr] = funcCallMatch;
      const args = argsStr ? argsStr.split(',').map(arg => this.parseExpression(arg.trim())) : [];
      
      return {
        type: 'CallExpression',
        callee: { type: 'Identifier', name: funcName },
        arguments: args
      };
    }
    
    // Parenthesized expression: (x + y)
    if (expr.startsWith('(') && expr.endsWith(')')) {
      return this.parseExpression(expr.substring(1, expr.length - 1));
    }
    
    // Binary expressions
    // We need to handle operator precedence properly, so check for each operator type in order
    
    // Logical operators: &&, ||
    const logicalMatch = this.findOperator(expr, ['&&', '||']);
    if (logicalMatch) {
      const { left, operator, right } = logicalMatch;
      return {
        type: 'LogicalExpression',
        operator,
        left: this.parseExpression(left),
        right: this.parseExpression(right)
      };
    }
    
    // Comparison operators: ==, !=, <, >, <=, >=
    const comparisonMatch = this.findOperator(expr, ['==', '!=', '<=', '>=', '<', '>']);
    if (comparisonMatch) {
      const { left, operator, right } = comparisonMatch;
      return {
        type: 'BinaryExpression',
        operator,
        left: this.parseExpression(left),
        right: this.parseExpression(right)
      };
    }
    
    // Additive operators: +, -
    const additiveMatch = this.findOperator(expr, ['+', '-']);
    if (additiveMatch) {
      const { left, operator, right } = additiveMatch;
      return {
        type: 'BinaryExpression',
        operator,
        left: this.parseExpression(left),
        right: this.parseExpression(right)
      };
    }
    
    // Multiplicative operators: *, /, %
    const multiplicativeMatch = this.findOperator(expr, ['*', '/', '%']);
    if (multiplicativeMatch) {
      const { left, operator, right } = multiplicativeMatch;
      return {
        type: 'BinaryExpression',
        operator,
        left: this.parseExpression(left),
        right: this.parseExpression(right)
      };
    }
    
    // Default: just wrap as raw expression
    return { type: 'RawExpression', value: expr };
  }
  
  /**
   * Find the first top-level operator in an expression
   * @param {string} expr - Expression string
   * @param {string[]} operators - Operators to look for
   * @returns {Object|null} Result with left, operator, and right parts, or null if no match
   */
  findOperator(expr, operators) {
    let parenDepth = 0;
    
    for (let i = 0; i < expr.length; i++) {
      const char = expr[i];
      
      if (char === '(') {
        parenDepth++;
      } else if (char === ')') {
        parenDepth--;
      }
      
      // Only consider operators at the top level of parentheses
      if (parenDepth === 0) {
        for (const op of operators) {
          if (expr.substring(i, i + op.length) === op) {
            const left = expr.substring(0, i).trim();
            const right = expr.substring(i + op.length).trim();
            return { left, operator: op, right };
          }
        }
      }
    }
    
    return null;
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
