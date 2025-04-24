import { StreamLanguage } from '@codemirror/language';
import { tags as t } from '@lezer/highlight';

// Custom language definition for SMT-LIB2
export const smt2 = {
  name: 'smt2',
  
  // Support file extensions
  fileExtensions: ['smt2', 'smt'],
  
  // Case sensitivity
  caseSensitive: false,
  
  // Comment syntax
  lineComment: ';',
  blockCommentStart: '#|',
  blockCommentEnd: '|#',

  // Token definitions
  tokenizer: {
    root: [
      // Whitespace and comments
      { regex: /\s+/, token: null },
      { regex: /;.*$/, token: 'comment' },
      { regex: /#\|/, token: 'comment', next: '@comment' },
      
      // Numbers
      { regex: /-?\d+\.\d+([eE][-+]?\d+)?/, token: 'number' },
      { regex: /-?\d+/, token: 'number' },
      { regex: /#x[0-9a-fA-F]+/, token: 'number' },
      { regex: /#b[01]+/, token: 'number' },
      
      // Strings
      { regex: /"(?:[^"\\]|\\.)*"/, token: 'string' },
      
      // Keywords
      { regex: /\b(assert|check-sat|declare-const|declare-fun|define-fun|exists|forall|let|match|set-logic|sat|unsat|unknown)\b/, token: 'keyword' },
      
      // Types
      { regex: /\b(Bool|Int|Real|Array|BitVec)\b/, token: 'type' },
      
      // Operators
      { regex: /\b(and|or|not|=>|=|distinct|ite|as|is)\b/, token: 'operator' },
      { regex: /[+\-*/<>=!&|^~:]+/, token: 'operator' },
      
      // Identifiers
      { regex: /[a-zA-Z_][\w._-]*/, token: 'variable' },
      
      // Parentheses
      { regex: /[\(\)]/, token: 'bracket' },
    ],
    
    comment: [
      { regex: /[^\|#]+/, token: 'comment' },
      { regex: /\|#/, token: 'comment', next: '@pop' },
      { regex: /./, token: 'comment' },
    ],
  },
  
  // Bracket handling
  brackets: [
    ['(', ')', 'bracket'],
  ],
  
  // Auto-indentation rules
  indentationRules: {
    increaseIndentPattern: /^\s*\(/,
    decreaseIndentPattern: /^\s*\)/,
  },

  // Map our tokens to CodeMirror styles
  styleName: {
    'comment': t.comment,
    'string': t.string,
    'number': t.number,
    'keyword': t.keyword,
    'type': t.typeName,
    'operator': t.operator,
    'variable': t.variableName,
    'bracket': t.bracket,
  },
};
