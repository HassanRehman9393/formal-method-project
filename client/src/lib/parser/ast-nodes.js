/**
 * Abstract Syntax Tree (AST) node definitions for the mini-language
 * 
 * This file defines the structure of each node type in our AST,
 * representing all language constructs supported by the parser.
 */

// Base node class with location tracking
export class Node {
  constructor(type) {
    this.type = type;
    this.location = null; // Will store start/end position in source
  }

  setLocation(location) {
    this.location = location;
    return this;
  }
}

// Program node - root of the AST
export class Program extends Node {
  constructor(statements) {
    super('Program');
    this.statements = statements || [];
  }
}

// Statement nodes

export class EmptyStatement extends Node {
  constructor() {
    super('EmptyStatement');
  }
}

export class BlockStatement extends Node {
  constructor(statements) {
    super('BlockStatement');
    this.statements = statements || [];
  }
}

export class AssignmentStatement extends Node {
  constructor(target, value) {
    super('AssignmentStatement');
    this.target = target; // Identifier or ArrayAccess
    this.value = value;   // Expression
  }
}

export class IfStatement extends Node {
  constructor(condition, thenBranch, elseBranch = null) {
    super('IfStatement');
    this.condition = condition;   // Expression
    this.thenBranch = thenBranch; // Statement
    this.elseBranch = elseBranch; // Statement or null
  }
}

export class WhileStatement extends Node {
  constructor(condition, body) {
    super('WhileStatement');
    this.condition = condition; // Expression
    this.body = body;          // Statement
  }
}

export class ForStatement extends Node {
  constructor(init, condition, update, body) {
    super('ForStatement');
    this.init = init;           // AssignmentStatement or null
    this.condition = condition;  // Expression or null
    this.update = update;        // AssignmentStatement or null
    this.body = body;           // Statement
  }
}

export class AssertStatement extends Node {
  constructor(condition) {
    super('AssertStatement');
    this.condition = condition; // Expression
  }
}

export class PostConditionStatement extends Node {
  constructor(condition) {
    super('PostConditionStatement');
    this.condition = condition; // Expression
  }
}

// Expression nodes

export class BinaryExpression extends Node {
  constructor(operator, left, right) {
    super('BinaryExpression');
    this.operator = operator; // String (e.g., '+', '-', '*', '&&', '==', etc.)
    this.left = left;        // Expression
    this.right = right;      // Expression
  }
}

export class UnaryExpression extends Node {
  constructor(operator, expression) {
    super('UnaryExpression');
    this.operator = operator;    // String (e.g., '-', '!')
    this.expression = expression; // Expression
  }
}

// Primary expressions

export class Identifier extends Node {
  constructor(name) {
    super('Identifier');
    this.name = name; // String
  }
}

export class ArrayAccess extends Node {
  constructor(array, index) {
    super('ArrayAccess');
    this.array = array; // Identifier
    this.index = index; // Expression
  }
}

export class IntegerLiteral extends Node {
  constructor(value) {
    super('IntegerLiteral');
    this.value = value; // Number
  }
}

export class BooleanLiteral extends Node {
  constructor(value) {
    super('BooleanLiteral');
    this.value = value; // Boolean
  }
}

// Helper function to create nodes with location information
export function createNode(NodeClass, location, ...args) {
  const node = new NodeClass(...args);
  return node.setLocation(location);
}
