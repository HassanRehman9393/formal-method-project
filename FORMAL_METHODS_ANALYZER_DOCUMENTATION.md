# Formal Methods Program Analyzer: Technical Documentation

## Overview

The Formal Methods Program Analyzer is a web-based tool for verifying program correctness and checking semantic equivalence between different implementations using formal methods. This document provides technical details about the system's implementation, components, and integration.

## Table of Contents

1. [Language Syntax and Semantics](#language-syntax-and-semantics)
2. [System Architecture](#system-architecture)
3. [Program Parsing](#program-parsing)
4. [SSA Transformation](#ssa-transformation)
5. [SMT Constraint Generation](#smt-constraint-generation)
6. [Z3 Solver Integration](#z3-solver-integration)
7. [User Interface Features](#user-interface-features)
8. [Integration Points](#integration-points)
9. [Limitations and Future Work](#limitations-and-future-work)

## Language Syntax and Semantics

### Mini-Language Specification

Our custom mini-language supports the following features:

```
// Variable declarations and assignments
x := 5;
y := x + 10;

// Arithmetic expressions
z := (x + y) * 2 / 3;

// Boolean expressions
b := x > 5 && y < 10;

// Conditional statements
if (x > 0) {
  y := x * 2;
} else {
  y := -x;
}

// Loop constructs
while (i < 10) {
  sum := sum + i;
  i := i + 1;
}

for (j := 0; j < 5; j := j + 1) {
  product := product * j;
}

// Arrays
arr[0] := 10;
arr[i+1] := arr[i] * 2;

// Assertions
assert(sum >= 0);
```

### Type System

The language supports:
- Integer values (default)
- Boolean values
- Arrays (integer indices and values)

### Semantics

- All variables are implicitly declared on first assignment
- Assignments have the form: `identifier := expression;`
- Array accesses have the form: `array[index] := expression;`
- Assertions are specified with: `assert(condition);`
- Loops can be bounded using the loop unrolling depth configuration

## System Architecture

The system follows a client-server architecture:

### Frontend (Client)
- React-based single-page application
- Modules: Code Editor, SSA Viewer, SMT Viewer, Results Viewer, Control Flow Graph Visualizer

### Backend (Server)
- Node.js with Express for API endpoints
- Modules: Parser, SSA Transformer, SMT Generator, Z3 Solver Interface

### API Endpoints
- `/api/parse`: Parses programs into AST
- `/api/parse/transform-ssa`: Transforms AST to SSA form
- `/api/verify`: Verifies assertions in a program
- `/api/verify/generate-smt`: Generates SMT constraints
- `/api/equivalence`: Checks program equivalence
- `/api/smt`: Manages SMT constraint generation

## Program Parsing

### Parser Implementation

The parser is implemented using a recursive descent approach with the following components:

1. **Lexical Analysis**: Tokenizes the input program
2. **Syntax Analysis**: Builds an Abstract Syntax Tree (AST)
3. **Semantic Analysis**: Checks for type correctness

### AST Structure

Each node in the AST has a `type` property along with type-specific properties:

```javascript
// Program node
{
  type: 'Program',
  body: [Statement]
}

// Variable declaration/assignment
{
  type: 'VariableDeclaration',
  id: { type: 'Identifier', name: 'x' },
  init: Expression
}

// If statement
{
  type: 'IfStatement',
  condition: Expression,
  consequent: [Statement],
  alternate: [Statement] | null
}
```

## SSA Transformation

### Static Single Assignment (SSA) Form

SSA form ensures each variable is assigned exactly once, making data flow analysis easier:

```
// Original code
x := 5;
x := x + 1;

// SSA form
x_0 := 5;
x_1 := x_0 + 1;
```

### Transformation Process

1. **Variable Versioning**: Assign unique version numbers to each variable assignment
2. **Phi Functions**: Insert at control flow merge points
3. **Loop Handling**: Unroll loops to a configurable depth

### Loop Unrolling

Loops are unrolled to a finite depth to enable verification:

```
// Original loop
while (i < 10) {
  sum := sum + i;
  i := i + 1;
}

// Unrolled (depth=2)
if (i_0 < 10) {
  sum_1 := sum_0 + i_0;
  i_1 := i_0 + 1;
  if (i_1 < 10) {
    sum_2 := sum_1 + i_1;
    i_2 := i_1 + 1;
  }
}
```

### SSA Optimizations

The SSA form is optimized using:
- **Constant Propagation**: Replace variables with known constants
- **Dead Code Elimination**: Remove unused variables and statements
- **Common Subexpression Elimination**: Reuse computed expressions

## SMT Constraint Generation

### SMT-LIB Format

The system generates SMT constraints in SMT-LIB format:

```
(declare-const x_0 Int)
(declare-const y_0 Int)
(assert (= x_0 5))
(assert (= y_0 (+ x_0 10)))
(assert (not (>= y_0 0)))  ; Negated assertion to find counterexamples
(check-sat)
(get-model)
```

### Constraint Generation Strategy

1. **Variable Declarations**: For each variable in SSA form
2. **Path Constraints**: For control flow decisions
3. **Assignment Constraints**: For variable assignments
4. **Array Constraints**: For array store and select operations
5. **Assertion Constraints**: Negated for counterexample finding

### Equivalence Checking

For equivalence checking:
1. Two programs are translated to SSA
2. Input variables are constrained to be equal
3. Output variables are constrained to be potentially different
4. The solver checks if there's any assignment that makes outputs different

## Z3 Solver Integration

### Z3 Solver Interface

The system interfaces with the Z3 theorem prover using:
- Direct execution of Z3 as a child process
- Parsing Z3's output to extract models and counterexamples

### Result Interpretation

- **UNSAT** result indicates verified assertions or program equivalence
- **SAT** result provides counterexamples for failed assertions or inequivalence

### Performance Optimizations

- **Constraint simplification**: Remove redundant constraints
- **Incremental solving**: Reuse solver state for similar queries
- **Timeout management**: Handle potential solver non-termination

## User Interface Features

### Code Editor

- Syntax highlighting for the mini-language
- Error highlighting with detailed messages
- Code completion suggestions

### Analysis Configuration

- Verification mode (assertion checking) or equivalence checking
- Loop unrolling depth configuration
- Optimization level selection

### SSA Visualization

- Side-by-side view of original code and SSA form
- Highlighting of optimizations applied
- Variable versioning visualization

### Control Flow Visualization

- Interactive control flow graph
- Path highlighting for counterexamples
- Zoom and pan for complex programs

### Results Presentation

- Clear success/failure indication
- Detailed counterexample display with variable values
- Execution trace for counterexamples

## Integration Points

### API Integration

The system's components integrate through well-defined API contracts:

1. **Parser → SSA Transformer**:
   - Input: Program code or AST
   - Output: SSA representation

2. **SSA Transformer → SMT Generator**:
   - Input: SSA representation
   - Output: SMT constraints

3. **SMT Generator → Z3 Solver**:
   - Input: SMT constraints
   - Output: Satisfiability result and model

4. **Solver → UI**:
   - Input: Verification result
   - Output: User-friendly presentation

### Data Flow Pipeline

The complete data flow through the system:
1. User inputs program code
2. Parser generates AST
3. SSA transformer converts to SSA form and applies optimizations
4. SMT generator creates constraints
5. Z3 solver checks constraints
6. Results are displayed to the user

## Limitations and Future Work

### Current Limitations

1. **Language Features**:
   - Limited support for complex data structures
   - No support for function definitions and calls
   - Limited type system

2. **Verification Capabilities**:
   - Loop unrolling limits the scope of verification
   - No support for loop invariants
   - Limited handling of recursive structures

3. **Performance**:
   - SMT solving can be slow for complex programs
   - Memory consumption for large constraint systems

### Future Enhancements

1. **Language Extensions**:
   - Add function definitions and calls
   - Support for more data types
   - Module system for larger programs

2. **Verification Capabilities**:
   - Loop invariant inference
   - Interprocedural analysis
   - Temporal property verification

3. **Performance Improvements**:
   - More aggressive constraint simplification
   - Parallel solving
   - Incremental verification for large programs

4. **User Interface**:
   - Interactive counterexample exploration
   - Step-by-step verification explanation
   - Integration with popular IDEs

---

*This documentation reflects the current state of the Formal Methods Program Analyzer as of the project completion date. For the latest updates and features, please refer to the project repository.* 