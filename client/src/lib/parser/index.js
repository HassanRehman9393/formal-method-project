/**
 * Unified Parser API for the mini-language
 * 
 * This module provides a clean interface to the parser functionality,
 * integrating the grammar, AST nodes, and error handling.
 */

import { parse, ParseError, validateAst } from './parser.js';
import * as ASTNodes from './ast-nodes.js';
import { visualizeAST } from './visualizer.js';

/**
 * Parse source code into an Abstract Syntax Tree
 * 
 * @param {string} source - The source code to parse
 * @param {object} options - Parser options
 * @param {boolean} options.validate - Whether to validate the AST for semantic errors
 * @return {object} The parsed AST
 * @throws {ParseError} If parsing fails
 */
function parseProgram(source, options = {}) {
  const ast = parse(source);
  
  // Add optional validation
  if (options.validate) {
    const errors = validateAst(ast);
    if (errors.length > 0) {
      const firstError = errors[0];
      throw new ParseError(
        firstError.message,
        firstError.location,
        source,
        null,
        null
      );
    }
  }
  
  return ast;
}

/**
 * Format an AST back to source code (partial implementation)
 * 
 * @param {object} ast - The AST to convert to source code
 * @return {string} The formatted source code
 */
function formatAST(ast) {
  // Simple implementation for now - can be expanded later
  function formatNode(node, indent = 0) {
    if (!node) return '';
    const spaces = ' '.repeat(indent);
    
    switch(node.type) {
      case 'Program':
        return node.statements.map(stmt => formatNode(stmt, indent)).join('\n');
      
      case 'AssignmentStatement':
        if (node.target.type === 'ArrayAccess') {
          const array = formatNode(node.target.array);
          const index = formatNode(node.target.index);
          const value = formatNode(node.value);
          return `${spaces}${array}[${index}] := ${value};`;
        } else {
          const target = formatNode(node.target);
          const value = formatNode(node.value);
          return `${spaces}${target} := ${value};`;
        }
      
      case 'IfStatement':
        let result = `${spaces}if (${formatNode(node.condition)}) {\n`;
        result += formatNode(node.thenBranch, indent + 2) + '\n';
        result += `${spaces}}`;
        if (node.elseBranch) {
          result += ` else {\n`;
          result += formatNode(node.elseBranch, indent + 2) + '\n';
          result += `${spaces}}`;
        }
        return result;
      
      case 'WhileStatement':
        return `${spaces}while (${formatNode(node.condition)}) {\n` +
               formatNode(node.body, indent + 2) + '\n' +
               `${spaces}}`;
      
      case 'ForStatement':
        let forStmt = `${spaces}for (`;
        forStmt += node.init ? formatNode(node.init).replace(/;$/, '') : '';
        forStmt += '; ';
        forStmt += node.condition ? formatNode(node.condition) : '';
        forStmt += '; ';
        forStmt += node.update ? formatNode(node.update).replace(/;$/, '') : '';
        forStmt += ') {\n';
        forStmt += formatNode(node.body, indent + 2) + '\n';
        forStmt += `${spaces}}`;
        return forStmt;
      
      case 'AssertStatement':
        return `${spaces}assert(${formatNode(node.condition)});`;
      
      case 'PostConditionStatement':
        return `${spaces}postcondition(${formatNode(node.condition)});`;
      
      case 'BlockStatement':
        if (node.statements.length === 0) return `${spaces}{}`;
        return `${spaces}{\n` +
               node.statements.map(stmt => formatNode(stmt, indent + 2)).join('\n') +
               `\n${spaces}}`;
      
      case 'EmptyStatement':
        return `${spaces};`;
      
      case 'BinaryExpression':
        return `${formatNode(node.left)} ${node.operator} ${formatNode(node.right)}`;
      
      case 'UnaryExpression':
        return `${node.operator}${formatNode(node.expression)}`;
      
      case 'Identifier':
        return node.name;
      
      case 'ArrayAccess':
        return `${formatNode(node.array)}[${formatNode(node.index)}]`;
      
      case 'IntegerLiteral':
        return node.value.toString();
      
      case 'BooleanLiteral':
        return node.value ? 'true' : 'false';
      
      default:
        return `<${node.type}>`;
    }
  }
  
  return formatAST(ast);
}

/**
 * Check if source code is syntactically valid
 * 
 * @param {string} source - The source code to validate
 * @return {boolean} True if valid, false otherwise
 */
function isValidSyntax(source) {
  try {
    parse(source);
    return true;
  } catch (e) {
    return false;
  }
}

export {
  parseProgram,
  formatAST,
  isValidSyntax,
  visualizeAST,
  ParseError,
  ASTNodes
};
