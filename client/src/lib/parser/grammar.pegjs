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
  = leading:OptWhitespace body:StatementList trailing:OptWhitespace {
      return {
        type: "Program",
        body: body,
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
        left: target,
        operator: ':=',
        right: value,
        location: location()
      };
    }

// Array assignment: arr[i] := expression;
ArrayAssignment
  = target:ArrayAccess OptWhitespace ":=" OptWhitespace value:Expression OptWhitespace ";" {
      return {
        type: "AssignmentStatement",
        left: target,
        operator: ':=',
        right: value,
        location: location()
      };
    }

// If-else statement: if (condition) statement else statement
IfStatement
  = "if" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace thenBranch:Statement elsePart:ElsePart? {
      return {
        type: "IfStatement",
        test: condition,
        consequent: thenBranch,
        alternate: elsePart,
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
        test: condition,
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
        test: condition,
        update: update,
        body: body,
        location: location()
      };
    }

ForInit
  = target:AssignmentTarget OptWhitespace ":=" OptWhitespace value:Expression {
      return {
        type: "AssignmentStatement",
        left: target,
        operator: ':=',
        right: value,
        location: location()
      };
    }

ForUpdate
  = target:AssignmentTarget OptWhitespace ":=" OptWhitespace value:Expression {
      return {
        type: "AssignmentStatement",
        left: target,
        operator: ':=',
        right: value,
        location: location()
      };
    }

// Assert statement: assert(expression);
AssertStatement
  = "assert" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace ";" {
      return {
        type: "AssertStatement",
        test: condition,
        location: location()
      };
    }

// Post-condition statement: postcondition(expression);
PostConditionStatement
  = "postcondition" OptWhitespace "(" OptWhitespace condition:Expression OptWhitespace ")" OptWhitespace ";" {
      return {
        type: "PostConditionStatement",
        test: condition,
        location: location()
      };
    }

// Block statement: { statement* }
BlockStatement
  = "{" OptWhitespace stmts:StatementList OptWhitespace "}" {
      return {
        type: "BlockStatement",
        body: stmts,
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

// Array access: arr[expr] (now with better support for nested array access)
ArrayAccess
  = array:Identifier indices:(
      OptWhitespace "[" OptWhitespace index:Expression OptWhitespace "]" {
        return index;
      }
    )+ {
      // Build the array access tree from left to right
      let result = array;
      for (let i = 0; i < indices.length; i++) {
        result = {
          type: "ArrayAccess",
          array: result,
          index: indices[i],
          location: location()
        };
      }
      return result;
    }

// Expression grammar with operator precedence
Expression
  = LogicalOrExpression

LogicalOrExpression
  = head:LogicalAndExpression
    tail:(
      OptWhitespace "||" OptWhitespace operand:LogicalAndExpression {
        return { operator: "||", operand: operand };
      }
    )* {
      return tail.reduce((left, { operator, operand }) => ({
        type: "BinaryExpression",
        operator: operator,
        left: left,
        right: operand,
        location: location()
      }), head);
    }

LogicalAndExpression
  = head:EqualityExpression
    tail:(
      OptWhitespace "&&" OptWhitespace operand:EqualityExpression {
        return { operator: "&&", operand: operand };
      }
    )* {
      return tail.reduce((left, { operator, operand }) => ({
        type: "BinaryExpression",
        operator: operator,
        left: left,
        right: operand,
        location: location()
      }), head);
    }

EqualityExpression
  = head:RelationalExpression
    tail:(
      OptWhitespace op:("==" / "!=") OptWhitespace operand:RelationalExpression {
        return { operator: op, operand: operand };
      }
    )* {
      return tail.reduce((left, { operator, operand }) => ({
        type: "BinaryExpression",
        operator: operator,
        left: left,
        right: operand,
        location: location()
      }), head);
    }

RelationalExpression
  = head:AdditiveExpression
    tail:(
      OptWhitespace op:("<=" / ">=" / "<" / ">") OptWhitespace operand:AdditiveExpression {
        return { operator: op, operand: operand };
      }
    )* {
      return tail.reduce((left, { operator, operand }) => ({
        type: "BinaryExpression",
        operator: operator,
        left: left,
        right: operand,
        location: location()
      }), head);
    }

AdditiveExpression
  = head:MultiplicativeExpression
    tail:(
      OptWhitespace op:("+" / "-") OptWhitespace operand:MultiplicativeExpression {
        return { operator: op, operand: operand };
      }
    )* {
      return tail.reduce((left, { operator, operand }) => ({
        type: "BinaryExpression",
        operator: operator,
        left: left,
        right: operand,
        location: location()
      }), head);
    }

MultiplicativeExpression
  = head:UnaryExpression
    tail:(
      OptWhitespace op:("*" / "/" / "%") OptWhitespace operand:UnaryExpression {
        return { operator: op, operand: operand };
      }
    )* {
      return tail.reduce((left, { operator, operand }) => ({
        type: "BinaryExpression",
        operator: operator,
        left: left,
        right: operand,
        location: location()
      }), head);
    }

UnaryExpression
  = op:("!" / "-") OptWhitespace operand:UnaryExpression {
      return {
        type: "UnaryExpression",
        operator: op,
        argument: operand,
        prefix: true,
        location: location()
      };
    }
  / ConditionalExpression

// Add support for ternary conditional expressions: condition ? thenExpr : elseExpr
ConditionalExpression
  = condition:PrimaryExpression OptWhitespace 
    "?" OptWhitespace thenExpr:Expression OptWhitespace 
    ":" OptWhitespace elseExpr:Expression {
      return {
        type: "ConditionalExpression",
        test: condition,
        consequent: thenExpr,
        alternate: elseExpr,
        location: location()
      };
    }
  / PrimaryExpression

PrimaryExpression
  = Literal
  / ArrayAccess
  / Identifier
  / ParenthesizedExpression

// Support for parenthesized expressions
ParenthesizedExpression
  = "(" OptWhitespace expr:Expression OptWhitespace ")" {
      // Preserve the expression type but mark that it was parenthesized
      return {
        ...expr,
        parenthesized: true
      };
    }

// Identifier: variable name
Identifier
  = name:IdentifierName {
      return {
        type: "Identifier",
        name: name,
        location: location()
      };
    }

IdentifierName
  = first:[a-zA-Z_] rest:[a-zA-Z0-9_]* {
      return first + rest.join("");
    }

// Literals: values
Literal
  = IntLiteral
  / BoolLiteral

// Integer literal
IntLiteral
  = digits:[0-9]+ {
      return {
        type: "IntLiteral",
        value: parseInt(digits.join(""), 10),
        raw: digits.join(""),
        location: location()
      };
    }

// Boolean literal
BoolLiteral
  = value:("true" / "false") {
      return {
        type: "BoolLiteral",
        value: value === "true",
        raw: value,
        location: location()
      };
    }

// Whitespace handling
OptWhitespace
  = Whitespace*

Whitespace
  = [ \t\n\r]
  / Comment

// Support for comments
Comment
  = SingleLineComment
  / MultiLineComment

SingleLineComment
  = "//" (!LineTerminator .)* (LineTerminator / EOF)

MultiLineComment
  = "/*" (!"*/" .)* "*/"

LineTerminator
  = [\n\r\u2028\u2029]

EOF
  = !.

// Helper rule for better error messages on missing semicolons
MissingSemicolon
  = !(";" / "}" / ")" / EOF) . {
      error("Missing semicolon");
    }
