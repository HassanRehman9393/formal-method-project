/**
 * PEG.js grammar for the mini-language
 * This defines the syntax for all language constructs
 */

// Import AST node types for use in semantic actions
{
  /* This section will be replaced with import statements during the build process */
  /* In a real implementation, we'd have a build step to inject these dependencies */
}

// Program is the starting rule
Program
  = leading:OptWhitespace stmts:StatementList trailing:OptWhitespace {
      return {
        type: "Program",
        statements: stmts,
        location: location()
      };
    }

StatementList
  = stmts:(Statement OptWhitespace)* {
      return stmts.map(s => s[0]).filter(s => s !== null);
    }

// A statement can be one of several types
Statement
  = AssignmentStatement
  / IfStatement
  / WhileStatement
  / ForStatement
  / AssertStatement
  / PostConditionStatement
  / BlockStatement
  / EmptyStatement

// Assignment statement: x := expression;
AssignmentStatement
  = SimpleAssignment
  / ArrayAssignment

// Simple assignment: x := expression;
SimpleAssignment
  = target:Identifier OptWhitespace ":=" OptWhitespace value:Expression OptWhitespace ";" {
      return {
        type: "AssignmentStatement",
        target: target,
        value: value,
        location: location()
      };
    }
  / target:Identifier OptWhitespace ":=" OptWhitespace value:AssignmentStatement {
      // Handle chained assignments: x := y := z := 10;
      return {
        type: "AssignmentStatement",
        target: target,
        value: value.value, // Get the final value from the right chain
        location: location()
      };
    }

// Array assignment: arr[i] := expression;
ArrayAssignment
  = target:ArrayAccess OptWhitespace ":=" OptWhitespace value:Expression OptWhitespace ";" {
      return {
        type: "AssignmentStatement",
        target: target,
        value: value,
        location: location()
      };
    }

// If-else statement: if (condition) statement else statement
IfStatement
  = "if" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace thenBranch:Statement elsePart:ElsePart? {
      return {
        type: "IfStatement",
        condition: condition,
        thenBranch: thenBranch,
        elseBranch: elsePart,
        location: location()
      };
    }

ElsePart
  = OptWhitespace "else" OptWhitespace statement:Statement {
      return statement;
    }

// While statement: while (condition) statement
WhileStatement
  = "while" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace body:Statement {
      return {
        type: "WhileStatement",
        condition: condition,
        body: body,
        location: location()
      };
    }

// For statement: for (init; condition; update) statement
ForStatement
  = "for" OptWhitespace "(" OptWhitespace 
    init:ForInit? OptWhitespace ";" OptWhitespace 
    condition:Expression? OptWhitespace ";" OptWhitespace 
    update:ForUpdate? OptWhitespace ")" OptWhitespace 
    body:Statement {
      return {
        type: "ForStatement",
        init: init,
        condition: condition,
        update: update,
        body: body,
        location: location()
      };
    }

ForInit
  = target:AssignmentTarget OptWhitespace ":=" OptWhitespace value:Expression {
      return {
        type: "AssignmentStatement",
        target: target,
        value: value,
        location: location()
      };
    }

ForUpdate
  = target:AssignmentTarget OptWhitespace ":=" OptWhitespace value:Expression {
      return {
        type: "AssignmentStatement",
        target: target,
        value: value,
        location: location()
      };
    }

// Assert statement: assert(expression);
AssertStatement
  = "assert" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace ";" {
      return {
        type: "AssertStatement",
        condition: condition,
        location: location()
      };
    }

// Post-condition statement: postcondition(expression);
PostConditionStatement
  = "postcondition" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace ";" {
      return {
        type: "PostConditionStatement",
        condition: condition,
        location: location()
      };
    }

// Block statement: { statement* }
BlockStatement
  = "{" OptWhitespace stmts:StatementList OptWhitespace "}" {
      return {
        type: "BlockStatement",
        statements: stmts,
        location: location()
      };
    }

// Empty statement: just a semicolon
EmptyStatement
  = ";" {
      return {
        type: "EmptyStatement",
        location: location()
      };
    }

// Assignment target - either an identifier or an array access
AssignmentTarget
  = Identifier
  / ArrayAccess

// Array access: arr[expr] or matrix[i][j]
ArrayAccess
  = base:NestedArrayAccess {
      return base;
    }

// Support for nested array access like matrix[i][j]
NestedArrayAccess
  = array:Identifier indices:(
      "[" OptWhitespace index:Expression OptWhitespace "]" {
        return index;
      }
    )+ {
      // Handle nested array access by chaining them
      return indices.reduce((acc, index) => ({
        type: "ArrayAccess",
        array: acc,
        index: index,
        location: location()
      }), array);
    }

// Expression hierarchy - follows order of operations
Expression
  = LogicalOrExpression

LogicalOrExpression
  = head:LogicalAndExpression tail:(OptWhitespace "||" OptWhitespace LogicalAndExpression)* {
      return tail.reduce((left, [, op, , right]) => ({
        type: "BinaryExpression",
        operator: op,
        left: left,
        right: right,
        location: location()
      }), head);
    }

LogicalAndExpression
  = head:EqualityExpression tail:(OptWhitespace "&&" OptWhitespace EqualityExpression)* {
      return tail.reduce((left, [, op, , right]) => ({
        type: "BinaryExpression",
        operator: op,
        left: left,
        right: right,
        location: location()
      }), head);
    }

EqualityExpression
  = head:RelationalExpression tail:(OptWhitespace ("==" / "!=") OptWhitespace RelationalExpression)* {
      return tail.reduce((left, [, op, , right]) => ({
        type: "BinaryExpression",
        operator: op,
        left: left,
        right: right,
        location: location()
      }), head);
    }

RelationalExpression
  = head:AdditiveExpression tail:(OptWhitespace ("<=" / ">=" / "<" / ">") OptWhitespace AdditiveExpression)* {
      return tail.reduce((left, [, op, , right]) => ({
        type: "BinaryExpression",
        operator: op,
        left: left,
        right: right,
        location: location()
      }), head);
    }

AdditiveExpression
  = head:MultiplicativeExpression tail:(OptWhitespace ("+" / "-") OptWhitespace MultiplicativeExpression)* {
      return tail.reduce((left, [, op, , right]) => ({
        type: "BinaryExpression",
        operator: op,
        left: left,
        right: right,
        location: location()
      }), head);
    }

MultiplicativeExpression
  = head:UnaryExpression tail:(OptWhitespace ("*" / "/" / "%") OptWhitespace UnaryExpression)* {
      return tail.reduce((left, [, op, , right]) => ({
        type: "BinaryExpression",
        operator: op,
        left: left,
        right: right,
        location: location()
      }), head);
    }

UnaryExpression
  = op:("!" / "-") OptWhitespace expr:UnaryExpression {
      return {
        type: "UnaryExpression",
        operator: op,
        expression: expr,
        location: location()
      };
    }
  / PrimaryExpression

PrimaryExpression
  = Literal
  / ArrayAccess
  / Identifier
  / "(" OptWhitespace expr:Expression OptWhitespace ")" { return expr; }

// Identifier
Identifier
  = name:$([a-zA-Z_][a-zA-Z0-9_]*) {
      return {
        type: "Identifier",
        name: name,
        location: location()
      };
    }

// Literals (integers and booleans)
Literal
  = IntegerLiteral
  / BooleanLiteral

IntegerLiteral
  = value:$([0-9]+) {
      return {
        type: "IntegerLiteral",
        value: parseInt(value, 10),
        location: location()
      };
    }

BooleanLiteral
  = value:"true" {
      return {
        type: "BooleanLiteral",
        value: true,
        location: location()
      };
    }
  / value:"false" {
      return {
        type: "BooleanLiteral",
        value: false,
        location: location()
      };
    }

// Mandatory whitespace (at least one space, tab, newline)
Whitespace
  = ([ \t\n\r]+ / Comment)

// Optional whitespace (zero or more spaces, tabs, newlines)
OptWhitespace
  = ([ \t\n\r] / Comment)*

Comment
  = "//" (![\n\r] .)* ([\n\r] / !.)
