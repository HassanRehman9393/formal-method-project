/**
 * Token definitions for the mini-language parser
 * These tokens will be used in building the PEG.js grammar
 */

// Token types
export const TokenType = {
  // Keywords
  KEYWORD_IF: 'if',
  KEYWORD_ELSE: 'else',
  KEYWORD_WHILE: 'while',
  KEYWORD_FOR: 'for',
  KEYWORD_ASSERT: 'assert',
  KEYWORD_TRUE: 'true',
  KEYWORD_FALSE: 'false',
  
  // Operators
  ASSIGN: ':=',
  PLUS: '+',
  MINUS: '-',
  MULTIPLY: '*',
  DIVIDE: '/',
  MODULO: '%',
  
  // Relational operators
  EQUAL: '==',
  NOT_EQUAL: '!=',
  LESS_THAN: '<',
  LESS_EQUAL: '<=',
  GREATER_THAN: '>',
  GREATER_EQUAL: '>=',
  
  // Logical operators
  LOGICAL_AND: '&&',
  LOGICAL_OR: '||',
  LOGICAL_NOT: '!',
  
  // Delimiters
  LEFT_PAREN: '(',
  RIGHT_PAREN: ')',
  LEFT_BRACE: '{',
  RIGHT_BRACE: '}',
  LEFT_BRACKET: '[',
  RIGHT_BRACKET: ']',
  SEMICOLON: ';',
  COMMA: ',',
  
  // Identifiers and literals
  IDENTIFIER: 'IDENTIFIER',
  INTEGER: 'INTEGER',
};

// Keywords map for quick lookup
export const keywords = {
  'if': TokenType.KEYWORD_IF,
  'else': TokenType.KEYWORD_ELSE,
  'while': TokenType.KEYWORD_WHILE,
  'for': TokenType.KEYWORD_FOR,
  'assert': TokenType.KEYWORD_ASSERT,
  'true': TokenType.KEYWORD_TRUE,
  'false': TokenType.KEYWORD_FALSE,
};

// Regular expression patterns for tokens
export const patterns = {
  identifier: /[a-zA-Z_][a-zA-Z0-9_]*/,
  integer: /[0-9]+/,
  whitespace: /\s+/,
  comment: /\/\/.*$/,
};
