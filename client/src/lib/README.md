# Formal Methods Program Analyzer Core Library

This directory contains the core implementation of the Formal Methods Program Analyzer, including the parser, SSA transformation, and optimization components.

## Components

The library is organized into these main components:

- **parser/**: Implementation of the mini-language parser
- **ssa/**: Static Single Assignment (SSA) transformation
- **optimizer/**: SSA optimizations
- **visualizer/**: Visualization utilities
- **smtgen/**: SMT constraint generation (to be integrated with Person 3's work)

## Test Suite

A comprehensive test suite has been implemented to ensure the reliability and correctness of the implementation. The tests cover:

### Parser Tests (`parser/parser-test.js`)
- Basic syntax parsing
- Control flow structures (if-else, loops)
- Array access and assignments
- Complex expressions
- Edge cases and error handling

### SSA Transformation Tests (`ssa/ssa-test.js`)
- Basic transformations
- Control flow handling
- Phi node placement
- Loop unrolling
- Array access in SSA form
- Edge cases

### Optimizer Tests (`optimizer/optimizer-test.js`)
- Constant propagation
- Dead code elimination
- Common subexpression elimination
- Full optimization pipeline
- Complex optimization scenarios

### Running Tests

To run all tests:
```
npm test
```

To run specific test suites:
```
npm run test:parser
npm run test:ssa
npm run test:optimizer
```

## Known Limitations and Edge Cases

### Parser Limitations
1. **Error Recovery**: The parser provides detailed error messages but has limited recovery capabilities.
2. **Complex Nested Expressions**: Very deeply nested expressions may cause performance issues.
3. **Comments**: Multi-line comments within expressions may cause unexpected behavior.

### SSA Transformation Limitations
1. **Loop Unrolling**: Loops are unrolled to a fixed depth, which may miss bugs that require more iterations.
2. **Variable Initialization**: Variables are assumed to be initialized before use.
3. **Recursive Data Structures**: Not supported in the current implementation.
4. **Memory Usage**: Large programs with many variables may consume significant memory.

### Optimizer Limitations
1. **Complex Control Flow**: Programs with complex control flow patterns may not optimize optimally.
2. **Array Optimizations**: Array accesses with variable indices have limited optimization potential.
3. **Optimization Conflicts**: Some optimizations may conflict with others in certain edge cases.

## Edge Cases Handled

1. **Empty Programs**: Properly handles programs with no statements.
2. **Undefined Variables**: Detects and reports variables used before assignment.
3. **Type Consistency**: While the language doesn't have explicit types, the analyzer enforces consistent usage.
4. **Array Bounds**: While bounds aren't checked at runtime, the analyzer can detect some out-of-bounds access patterns.
5. **Control Flow Merge Points**: Correctly handles variable versions at control flow merge points.
6. **Conditional Analysis**: Handles the interactions between conditions and subsequent code.

## Future Improvements

1. **More Efficient SSA Algorithm**: Implement an SSA construction algorithm with better performance characteristics.
2. **Symbolic Loop Handling**: Handle loops symbolically instead of unrolling for certain verification tasks.
3. **Better Array Analysis**: Implement more sophisticated array dependence analysis.
4. **Additional Optimizations**: Implement more advanced optimizations like loop invariant code motion and partial redundancy elimination.
5. **Incremental Parsing**: Support incremental parsing for better editor integration.
6. **Better Error Recovery**: Enhance the parser to recover from more types of syntax errors.

## Performance Considerations

For optimal performance when working with the library:

1. Keep loop unrolling depth as small as necessary for verification.
2. Complex array operations may generate large SMT constraints.
3. Programs with many variables and complex control flow will generate larger SSA representations.
4. The optimization pipeline may be time-consuming for very large programs. 