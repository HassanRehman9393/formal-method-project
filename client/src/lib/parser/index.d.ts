/**
 * Type definitions for the parser module
 */

/**
 * AST Node types
 */
export interface ASTNode {
  type: string;
  [key: string]: any;
}

export interface Program extends ASTNode {
  type: 'Program';
  body: Statement[];
}

export interface Statement extends ASTNode {
  type: string;
}

export interface Expression extends ASTNode {
  type: string;
}

export interface AssignmentStatement extends Statement {
  type: 'AssignmentStatement';
  left: Expression;
  right: Expression;
}

export interface IfStatement extends Statement {
  type: 'IfStatement';
  condition: Expression;
  consequent: Statement[];
  alternate?: Statement[];
}

export interface WhileStatement extends Statement {
  type: 'WhileStatement';
  condition: Expression;
  body: Statement[];
}

export interface ForStatement extends Statement {
  type: 'ForStatement';
  init: Statement;
  condition: Expression;
  update: Statement;
  body: Statement[];
}

export interface AssertStatement extends Statement {
  type: 'AssertStatement';
  argument: Expression;
}

export interface BinaryExpression extends Expression {
  type: 'BinaryExpression';
  operator: string;
  left: Expression;
  right: Expression;
}

export interface Identifier extends Expression {
  type: 'Identifier';
  name: string;
}

export interface Literal extends Expression {
  type: 'Literal';
  value: number | boolean | string | null;
  raw: string;
}

export interface ArrayAccess extends Expression {
  type: 'ArrayAccess';
  array: Identifier;
  index: Expression;
}

/**
 * Parse a program string into an AST
 * @param program The input program string
 * @returns AST representing the program
 */
export function parse(program: string): Program;

/**
 * Visualize an AST
 * @param ast The AST to visualize
 * @returns HTML string representation of the AST
 */
export function visualizeAST(ast: Program): string;

/**
 * Format error from the parser
 * @param error The parser error
 * @returns Formatted error message
 */
export function formatError(error: any): string; 