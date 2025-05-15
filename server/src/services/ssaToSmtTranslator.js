/**
 * SSA to SMT Translator
 * Translates programs in SSA form to SMT constraints
 */

/**
 * Translate SSA AST to SMT constraints
 * @param {Object} ast - AST in SSA form
 * @param {Object} options - Translation options
 * @returns {Object} SMT translation result
 */
exports.translate = async function(ast, options = {}) {
  try {
    const {
      variables = [],
      arrays = [],
      assertions = [],
      loopUnrollDepth = 5,
      outputPrefix = ''
    } = options;

    // Initialize result
    const result = {
      declarations: [],
      assertions: [],
      statements: [],
      variables: []
    };

    // Process variables
    const variableMap = new Map();
    variables.forEach(variable => {
      const name = typeof variable === 'string' ? variable : variable.name;
      const type = variable.type || 'Int';
      
      // Initial variable
      const varName = `${outputPrefix}${name}`;
      result.declarations.push(`(declare-const ${varName} ${type})`);
      
      // Final variable state after execution
      const finalVarName = `${outputPrefix}${name}_final`;
      result.declarations.push(`(declare-const ${finalVarName} ${type})`);
      
      // Track all versions of this variable
      variableMap.set(name, {
        versions: [varName],
        finalName: finalVarName,
        type
      });
      
      result.variables.push(varName);
    });
    
    // Process arrays
    const arrayMap = new Map();
    arrays.forEach(array => {
      const name = typeof array === 'string' ? array : array.name;
      const size = array.size || 10;
      const elementType = array.elementType || 'Int';
      
      // Array type declaration
      const arrayType = `(Array Int ${elementType})`;
      
      // Initial array
      const arrayName = `${outputPrefix}${name}`;
      result.declarations.push(`(declare-const ${arrayName} ${arrayType})`);
      
      // Final array state after execution
      const finalArrayName = `${outputPrefix}${name}_final`;
      result.declarations.push(`(declare-const ${finalArrayName} ${arrayType})`);
      
      // Track all versions of this array
      arrayMap.set(name, {
        versions: [arrayName],
        finalName: finalArrayName,
        type: arrayType
      });
    });
    
    // Generate constraints from AST
    const constraints = translateASTToSMT(ast, {
      variableMap,
      arrayMap,
      outputPrefix,
      loopUnrollDepth
    });
    
    // Add constraints to result
    result.declarations = [...result.declarations, ...constraints.declarations];
    result.assertions = [...result.assertions, ...constraints.assertions];
    result.statements = constraints.statements;
    
    // Add final state constraints
    addFinalStateConstraints(result, variableMap, arrayMap);
    
    return result;
  } catch (error) {
    console.error('Error in SSA to SMT translation:', error);
    throw error;
  }
};

/**
 * Translate AST to SMT constraints
 * @param {Object} ast - Program AST
 * @param {Object} context - Translation context
 * @returns {Object} Generated constraints
 */
function translateASTToSMT(ast, context) {
  const { variableMap, arrayMap, outputPrefix, loopUnrollDepth } = context;
  
  // Initialize result
  const result = {
    declarations: [],
    assertions: [],
    statements: []
  };
  
  // Process all statements in program
  if (ast.body && Array.isArray(ast.body)) {
    // Create control flow path constraints
    let pathCondition = 'true';
    
    // Process each statement in sequence
    for (const statement of ast.body) {
      const stmtResult = translateStatement(statement, {
        variableMap,
        arrayMap,
        outputPrefix,
        pathCondition,
        loopUnrollDepth
      });
      
      // Add results from this statement
      result.declarations = [...result.declarations, ...stmtResult.declarations];
      result.assertions = [...result.assertions, ...stmtResult.assertions];
      result.statements = [...result.statements, ...stmtResult.statements];
      
      // Update path condition
      pathCondition = stmtResult.pathCondition || pathCondition;
    }
  }
  
  return result;
}

/**
 * Translate a statement to SMT
 * @param {Object} statement - Statement node
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints for this statement
 */
function translateStatement(statement, context) {
  const { variableMap, arrayMap, outputPrefix, pathCondition, loopUnrollDepth } = context;
  
  // Default result structure
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition: pathCondition
  };
  
  if (!statement) return result;
  
  // Process different statement types
  switch (statement.type) {
    case 'VariableDeclaration':
    case 'AssignmentStatement':
      return translateAssignment(statement, context);
      
    case 'IfStatement':
      return translateIfStatement(statement, context);
      
    case 'WhileStatement':
      return translateWhileStatement(statement, context);
      
    case 'ForStatement':
      return translateForStatement(statement, context);
      
    case 'AssertStatement':
      return translateAssertStatement(statement, context);
      
    case 'Block':
      return translateBlock(statement, context);
      
    default:
      console.warn(`Unhandled statement type: ${statement.type}`);
      return result;
  }
}

/**
 * Translate assignment statement to SMT
 * @param {Object} statement - Assignment statement
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints
 */
function translateAssignment(statement, context) {
  const { variableMap, arrayMap, outputPrefix, pathCondition } = context;
  
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition: pathCondition
  };
  
  try {
    // Determine variable name and expression
    let varName, expression, isArrayAssignment = false;
    let arrayName, indexExpr;
    
    if (statement.type === 'VariableDeclaration') {
      varName = statement.id.name;
      expression = statement.init;
    } else if (statement.type === 'AssignmentStatement') {
      if (statement.left.type === 'Identifier') {
        varName = statement.left.name;
        expression = statement.right;
      } else if (statement.left.type === 'MemberExpression') {
        // Array assignment: arr[index] := value
        isArrayAssignment = true;
        arrayName = statement.left.object.name;
        indexExpr = statement.left.property;
        expression = statement.right;
      }
    }
    
    if (isArrayAssignment) {
      // Handle array assignment
      if (arrayMap.has(arrayName)) {
        const arrayInfo = arrayMap.get(arrayName);
        const currentVersion = arrayInfo.versions[arrayInfo.versions.length - 1];
        const newVersion = `${outputPrefix}${arrayName}_${arrayInfo.versions.length}`;
        
        // Declare new array version
        result.declarations.push(`(declare-const ${newVersion} ${arrayInfo.type})`);
        
        // Convert expressions to SMT
        const indexSMT = expressionToSMT(indexExpr, context);
        const valueSMT = expressionToSMT(expression, context);
        
        // Create array store constraint
        result.assertions.push({
          constraint: `(= ${newVersion} (store ${currentVersion} ${indexSMT} ${valueSMT}))`,
          description: `Array assignment: ${arrayName}[${indexSMT}] := ${valueSMT}`
        });
        
        // Update array versions
        arrayInfo.versions.push(newVersion);
      }
    } else if (varName) {
      // Handle regular variable assignment
      if (!variableMap.has(varName)) {
        // If variable doesn't exist yet, add it
        variableMap.set(varName, {
          versions: [`${outputPrefix}${varName}`],
          finalName: `${outputPrefix}${varName}_final`,
          type: 'Int'
        });
        
        // Declare the variable
        result.declarations.push(`(declare-const ${outputPrefix}${varName} Int)`);
        result.declarations.push(`(declare-const ${outputPrefix}${varName}_final Int)`);
      }
      
      // Get variable info
      const varInfo = variableMap.get(varName);
      
      // Create new version for this assignment
      const newVersion = `${outputPrefix}${varName}_${varInfo.versions.length}`;
      
      // Declare new version
      result.declarations.push(`(declare-const ${newVersion} ${varInfo.type})`);
      
      // Convert expression to SMT
      const exprSMT = expressionToSMT(expression, context);
      
      // Add constraint for this assignment
      result.assertions.push({
        constraint: `(= ${newVersion} ${exprSMT})`,
        description: `Assignment: ${varName} := ${exprSMT}`
      });
      
      // Update variable versions
      varInfo.versions.push(newVersion);
    }
    
    return result;
  } catch (error) {
    console.error('Error in translateAssignment:', error);
    return result;
  }
}

/**
 * Translate if statement to SMT
 * @param {Object} statement - If statement
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints
 */
function translateIfStatement(statement, context) {
  const { pathCondition } = context;
  
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition
  };
  
  try {
    // Translate condition to SMT
    const conditionSMT = expressionToSMT(statement.condition, context);
    
    // Create context for true branch
    const trueContext = {
      ...context,
      pathCondition: `(and ${pathCondition} ${conditionSMT})`
    };
    
    // Process true branch
    const trueResult = translateStatement(statement.consequent, trueContext);
    
    // Add results from true branch
    result.declarations = [...result.declarations, ...trueResult.declarations];
    result.assertions = [...result.assertions, ...trueResult.assertions];
    result.statements = [...result.statements, ...trueResult.statements];
    
    // Process false branch if it exists
    if (statement.alternate) {
      // Create context for false branch
      const falseContext = {
        ...context,
        pathCondition: `(and ${pathCondition} (not ${conditionSMT}))`
      };
      
      // Process false branch
      const falseResult = translateStatement(statement.alternate, falseContext);
      
      // Add results from false branch
      result.declarations = [...result.declarations, ...falseResult.declarations];
      result.assertions = [...result.assertions, ...falseResult.assertions];
      result.statements = [...result.statements, ...falseResult.statements];
    }
    
    return result;
  } catch (error) {
    console.error('Error in translateIfStatement:', error);
    return result;
  }
}

/**
 * Translate while statement to SMT with loop unrolling
 * @param {Object} statement - While statement
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints
 */
function translateWhileStatement(statement, context) {
  const { loopUnrollDepth, pathCondition } = context;
  
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition
  };
  
  try {
    // Unroll the loop
    let currentContext = { ...context };
    
    for (let i = 0; i < loopUnrollDepth; i++) {
      // Translate condition to SMT
      const conditionSMT = expressionToSMT(statement.condition, currentContext);
      
      // Create context for loop body
      const bodyContext = {
        ...currentContext,
        pathCondition: `(and ${currentContext.pathCondition} ${conditionSMT})`
      };
      
      // Check if loop condition can be true
      const loopExitContext = {
        ...currentContext,
        pathCondition: `(and ${currentContext.pathCondition} (not ${conditionSMT}))`
      };
      
      // Add loop exit condition
      if (i === loopUnrollDepth - 1) {
        // For the last iteration, assert the loop must terminate
        // This prevents infinite loops from being verified
        result.assertions.push({
          constraint: `(=> ${bodyContext.pathCondition} (not ${conditionSMT}))`,
          description: `Loop termination after ${loopUnrollDepth} iterations`
        });
      }
      
      // If loop condition can be true, process body
      const bodyResult = translateStatement(statement.body, bodyContext);
      
      // Add results from this iteration
      result.declarations = [...result.declarations, ...bodyResult.declarations];
      result.assertions = [...result.assertions, ...bodyResult.assertions];
      result.statements = [...result.statements, ...bodyResult.statements];
      
      // Update context for next iteration
      currentContext = {
        ...currentContext,
        pathCondition: bodyResult.pathCondition
      };
    }
    
    return result;
  } catch (error) {
    console.error('Error in translateWhileStatement:', error);
    return result;
  }
}

/**
 * Translate for statement to SMT with loop unrolling
 * @param {Object} statement - For statement
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints
 */
function translateForStatement(statement, context) {
  const { loopUnrollDepth } = context;
  
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition: context.pathCondition
  };
  
  try {
    // First, process the initialization
    let currentContext = { ...context };
    
    if (statement.init) {
      const initResult = translateStatement(statement.init, currentContext);
      
      // Add results from initialization
      result.declarations = [...result.declarations, ...initResult.declarations];
      result.assertions = [...result.assertions, ...initResult.assertions];
      result.statements = [...result.statements, ...initResult.statements];
      
      // Update context after initialization
      currentContext = {
        ...currentContext,
        pathCondition: initResult.pathCondition
      };
    }
    
    // Unroll the loop
    for (let i = 0; i < loopUnrollDepth; i++) {
      // Check loop condition if provided
      if (statement.condition) {
        const conditionSMT = expressionToSMT(statement.condition, currentContext);
        
        // Create context for loop body
        const bodyContext = {
          ...currentContext,
          pathCondition: `(and ${currentContext.pathCondition} ${conditionSMT})`
        };
        
        // Check if loop condition can be true
        const loopExitContext = {
          ...currentContext,
          pathCondition: `(and ${currentContext.pathCondition} (not ${conditionSMT}))`
        };
        
        // If this is the last iteration, assert the loop must terminate
        if (i === loopUnrollDepth - 1) {
          result.assertions.push({
            constraint: `(=> ${bodyContext.pathCondition} (not ${conditionSMT}))`,
            description: `For loop termination after ${loopUnrollDepth} iterations`
          });
        }
        
        // Process loop body
        const bodyResult = translateStatement(statement.body, bodyContext);
        
        // Add results from this iteration body
        result.declarations = [...result.declarations, ...bodyResult.declarations];
        result.assertions = [...result.assertions, ...bodyResult.assertions];
        result.statements = [...result.statements, ...bodyResult.statements];
        
        // Update context after body
        currentContext = {
          ...currentContext,
          pathCondition: bodyResult.pathCondition
        };
      } else {
        // If no condition, always execute body
        const bodyResult = translateStatement(statement.body, currentContext);
        
        // Add results from this iteration body
        result.declarations = [...result.declarations, ...bodyResult.declarations];
        result.assertions = [...result.assertions, ...bodyResult.assertions];
        result.statements = [...result.statements, ...bodyResult.statements];
        
        // Update context after body
        currentContext = {
          ...currentContext,
          pathCondition: bodyResult.pathCondition
        };
      }
      
      // Process update (increment) if provided
      if (statement.update) {
        const updateResult = translateStatement(statement.update, currentContext);
        
        // Add results from update
        result.declarations = [...result.declarations, ...updateResult.declarations];
        result.assertions = [...result.assertions, ...updateResult.assertions];
        result.statements = [...result.statements, ...updateResult.statements];
        
        // Update context after update
        currentContext = {
          ...currentContext,
          pathCondition: updateResult.pathCondition
        };
      }
    }
    
    return result;
  } catch (error) {
    console.error('Error in translateForStatement:', error);
    return result;
  }
}

/**
 * Translate assert statement to SMT
 * @param {Object} statement - Assert statement
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints
 */
function translateAssertStatement(statement, context) {
  const { pathCondition } = context;
  
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition
  };
  
  try {
    // Translate assertion expression to SMT
    const assertionSMT = expressionToSMT(statement.expression, context);
    
    // Add assertion as a negation to check for counterexamples
    // We negate the assertion and add it to the constraints
    // If the solver returns SAT, it means the assertion can be violated
    result.assertions.push({
      constraint: `(and ${pathCondition} (not ${assertionSMT}))`,
      description: `Assert: ${assertionSMT}`,
      isAssertion: true
    });
    
    return result;
  } catch (error) {
    console.error('Error in translateAssertStatement:', error);
    return result;
  }
}

/**
 * Translate block statement to SMT
 * @param {Object} statement - Block statement
 * @param {Object} context - Translation context
 * @returns {Object} SMT constraints
 */
function translateBlock(statement, context) {
  const { pathCondition } = context;
  
  const result = {
    declarations: [],
    assertions: [],
    statements: [statement],
    pathCondition
  };
  
  try {
    // Process each statement in the block
    if (statement.body && Array.isArray(statement.body)) {
      let currentContext = { ...context };
      
      for (const stmt of statement.body) {
        const stmtResult = translateStatement(stmt, currentContext);
        
        // Add results from this statement
        result.declarations = [...result.declarations, ...stmtResult.declarations];
        result.assertions = [...result.assertions, ...stmtResult.assertions];
        result.statements = [...result.statements, ...stmtResult.statements];
        
        // Update context for next statement
        currentContext = {
          ...currentContext,
          pathCondition: stmtResult.pathCondition
        };
      }
    }
    
    return result;
  } catch (error) {
    console.error('Error in translateBlock:', error);
    return result;
  }
}

/**
 * Convert expression to SMT format
 * @param {Object} expr - Expression node
 * @param {Object} context - Translation context
 * @returns {string} SMT expression
 */
function expressionToSMT(expr, context) {
  if (!expr) return 'true';
  
  const { variableMap, arrayMap, outputPrefix } = context;
  
  try {
    switch (expr.type) {
      case 'Literal':
        // Handle literal values
        if (typeof expr.value === 'boolean') {
          return expr.value ? 'true' : 'false';
        } else {
          return expr.value.toString();
        }
        
      case 'Identifier':
        // Handle variable references
        if (variableMap.has(expr.name)) {
          const varInfo = variableMap.get(expr.name);
          // Return the latest version of the variable
          return varInfo.versions[varInfo.versions.length - 1];
        }
        return expr.name;
        
      case 'BinaryExpression':
        // Handle binary operations
        const left = expressionToSMT(expr.left, context);
        const right = expressionToSMT(expr.right, context);
        
        // Map operator to SMT
        let operator;
        switch (expr.operator) {
          case '+': operator = '+'; break;
          case '-': operator = '-'; break;
          case '*': operator = '*'; break;
          case '/': operator = 'div'; break;
          case '%': operator = 'mod'; break;
          case '==': operator = '='; break;
          case '!=': operator = 'distinct'; break;
          case '<': operator = '<'; break;
          case '<=': operator = '<='; break;
          case '>': operator = '>'; break;
          case '>=': operator = '>='; break;
          case '&&': operator = 'and'; break;
          case '||': operator = 'or'; break;
          default: operator = expr.operator;
        }
        
        return `(${operator} ${left} ${right})`;
        
      case 'UnaryExpression':
        // Handle unary operations
        const arg = expressionToSMT(expr.argument, context);
        
        // Map operator to SMT
        let unaryOp;
        switch (expr.operator) {
          case '!': unaryOp = 'not'; break;
          case '-': unaryOp = '-'; break;
          default: unaryOp = expr.operator;
        }
        
        return `(${unaryOp} ${arg})`;
        
      case 'MemberExpression':
        // Handle array access: array[index]
        const array = expr.object.name;
        const index = expressionToSMT(expr.property, context);
        
        if (arrayMap.has(array)) {
          const arrayInfo = arrayMap.get(array);
          // Use the latest version of the array
          const currentVersion = arrayInfo.versions[arrayInfo.versions.length - 1];
          return `(select ${currentVersion} ${index})`;
        }
        
        return `(select ${array} ${index})`;
        
      case 'LogicalExpression':
        // Handle logical operations
        const leftExpr = expressionToSMT(expr.left, context);
        const rightExpr = expressionToSMT(expr.right, context);
        
        // Map operator to SMT
        let logicalOp;
        switch (expr.operator) {
          case '&&': logicalOp = 'and'; break;
          case '||': logicalOp = 'or'; break;
          default: logicalOp = expr.operator;
        }
        
        return `(${logicalOp} ${leftExpr} ${rightExpr})`;
        
      case 'ForComprehension':
        // Handle Python-like comprehension assertions for array sortedness
        try {
          // Extract array name from the condition
          let arrayName = null;
          if (expr.condition && expr.condition.type === 'MemberExpression' && 
              expr.condition.object && expr.condition.object.name) {
            arrayName = expr.condition.object.name;
          } else if (expr.condition) {
            // Try to extract from more complex conditions
            const condStr = JSON.stringify(expr.condition);
            const arrayMatch = condStr.match(/"name":"(\w+)"/);
            if (arrayMatch) {
              arrayName = arrayMatch[1];
            }
          }
          
          // If we found an array, generate sortedness constraints
          if (arrayName && arrayMap.has(arrayName)) {
            const arrayInfo = arrayMap.get(arrayName);
            const currentVersion = arrayInfo.versions[arrayInfo.versions.length - 1];
            
            // Generate a constraint that checks if the array is sorted
            // For simplicity, we'll check a[0] <= a[1] && a[1] <= a[2] && ...
            const indices = [0, 1, 2, 3]; // Use a reasonable number of indices
            const constraints = [];
            
            for (let i = 0; i < indices.length - 1; i++) {
              constraints.push(
                `(<= (select ${currentVersion} ${indices[i]}) (select ${currentVersion} ${indices[i + 1]}))`
              );
            }
            
            if (constraints.length > 0) {
              return `(and ${constraints.join(' ')})`;
            }
            return 'true';
          }
          
          // Fallback for unknown arrays
          return 'true';
        } catch (error) {
          console.error('Error handling ForComprehension:', error);
          return 'true';
        }
        
      default:
        console.warn(`Unhandled expression type: ${expr.type}`);
        return expr.toString();
    }
  } catch (error) {
    console.error('Error in expressionToSMT:', error);
    return 'error';
  }
}

/**
 * Add constraints for final state of variables and arrays
 * @param {Object} result - SMT result object
 * @param {Map} variableMap - Map of variables and their versions
 * @param {Map} arrayMap - Map of arrays and their versions
 */
function addFinalStateConstraints(result, variableMap, arrayMap) {
  // Add constraints for final variable values
  variableMap.forEach((varInfo, varName) => {
    if (varInfo.versions.length > 0) {
      const finalValue = varInfo.versions[varInfo.versions.length - 1];
      
      // Connect the final version to the _final variable
      result.assertions.push({
        constraint: `(= ${varInfo.finalName} ${finalValue})`,
        description: `Final value of ${varName}`
      });
    }
  });
  
  // Add constraints for final array values
  arrayMap.forEach((arrayInfo, arrayName) => {
    if (arrayInfo.versions.length > 0) {
      const finalValue = arrayInfo.versions[arrayInfo.versions.length - 1];
      
      // Connect the final version to the _final array
      result.assertions.push({
        constraint: `(= ${arrayInfo.finalName} ${finalValue})`,
        description: `Final state of array ${arrayName}`
      });
    }
  });
}
