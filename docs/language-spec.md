# Mini-Language Specification

## 1. Overview

This document outlines the specification for our custom mini-language used in the Formal Methods Program Analyzer. The language is designed to be simple yet expressive enough to demonstrate program verification concepts.

## 2. Lexical Elements (Tokens)

### 2.1 Keywords
- `if`, `else` - Conditional statements
- `while`, `for` - Loop constructs
- `assert` - Assertion statement
- `true`, `false` - Boolean literals

### 2.2 Operators
- **Assignment**: `:=`
- **Arithmetic**: `+`, `-`, `*`, `/`, `%` (modulo)
- **Relational**: `==`, `!=`, `<`, `<=`, `>`, `>=`
- **Logical**: `&&` (and), `||` (or), `!` (not)
- **Array Access**: `[]`
- **Parentheses**: `(`, `)`
- **Braces**: `{`, `}`
- **Semicolon**: `;`
- **Comma**: `,`

### 2.3 Identifiers
Variable names begin with a letter or underscore followed by any combination of letters, digits, or underscores.

**Regex**: `[a-zA-Z_][a-zA-Z0-9_]*`

### 2.4 Literals
- **Integers**: Sequence of digits, e.g., `123`
- **Booleans**: `true`, `false`

## 3. Grammar Specification

Using a context-free grammar notation similar to BNF:

```
Program     ::= Statement*

Statement   ::= AssignmentStmt
              | IfStmt
              | WhileStmt
              | ForStmt
              | AssertStmt
              | Block
              | ";" // Empty statement

AssignmentStmt ::= Identifier ":=" Expression ";"
                 | Identifier "[" Expression "]" ":=" Expression ";"

IfStmt      ::= "if" "(" Expression ")" Statement ("else" Statement)?

WhileStmt   ::= "while" "(" Expression ")" Statement

ForStmt     ::= "for" "(" AssignmentStmt? ";" Expression? ";" AssignmentStmt? ")" Statement

AssertStmt  ::= "assert" "(" Expression ")" ";"

Block       ::= "{" Statement* "}"

Expression  ::= LogicalOrExpr

LogicalOrExpr ::= LogicalAndExpr ("||" LogicalAndExpr)*

LogicalAndExpr ::= EqualityExpr ("&&" EqualityExpr)*

EqualityExpr ::= RelationalExpr (("==" | "!=") RelationalExpr)*

RelationalExpr ::= AdditiveExpr (("<" | "<=" | ">" | ">=") AdditiveExpr)*

AdditiveExpr ::= MultiplicativeExpr (("+" | "-") MultiplicativeExpr)*

MultiplicativeExpr ::= UnaryExpr (("*" | "/" | "%") UnaryExpr)*

UnaryExpr   ::= ("!" | "-") UnaryExpr
              | PrimaryExpr

PrimaryExpr ::= Identifier
              | Identifier "[" Expression "]"
              | Literal
              | "(" Expression ")"

Identifier  ::= [a-zA-Z_][a-zA-Z0-9_]*

Literal     ::= IntLiteral
              | BoolLiteral

IntLiteral  ::= [0-9]+

BoolLiteral ::= "true" | "false"
```

## 4. Syntax Examples

### 4.1 Variable Declaration and Assignment

```
// Variable declarations with initialization
x := 5;
y := x + 3;
flag := true;

// Array assignment
arr[0] := 42;
arr[i+1] := arr[i] * 2;
```

### 4.2 Conditional Statements

```
if (x > 0) {
    y := x;
} else {
    y := -x;
}

// Single statement if
if (flag) x := 1;
```

### 4.3 Loop Structures

```
// While loop
i := 0;
while (i < 10) {
    sum := sum + i;
    i := i + 1;
}

// For loop
for (i := 0; i < 10; i := i + 1) {
    sum := sum + i;
}
```

### 4.4 Assertions

```
x := 5;
y := x * 2;
assert(y == 10);

// Complex assertion
assert(x >= 0 && y == x * 2);
```

### 4.5 Complex Example

```
// Compute sum of array elements
sum := 0;
for (i := 0; i < n; i := i + 1) {
    sum := sum + arr[i];
}

// Verify the sum is correct
expected := (n * (n-1)) / 2;  // Assuming array contains 0,1,...,n-1
assert(sum == expected);
```

## 5. Limitations and Restrictions

- No function definitions or calls
- No floating-point numbers
- No string types
- Variable declarations are implicit (first assignment)
- Arrays have no explicit size declarations
- No built-in I/O operations
- No exception handling mechanisms

## 6. Semantic Rules

- Variables must be assigned before use
- Array indices must evaluate to integers
- Boolean expressions are required in conditional and loop conditions
- Arrays are zero-indexed
- No type checking (all variables assumed to be compatible)
