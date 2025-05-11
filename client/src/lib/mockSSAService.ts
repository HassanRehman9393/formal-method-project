/**
 * This file provides mock services for generating AST and SSA related data
 * Used as fallbacks when real data isn't available from the backend
 */

// Simple mock AST generation
export const generateMockAST = (program: string): any => {
  // Create a simple AST structure based on program content
  const lines = program.split('\n').filter(line => line.trim());
  
  // Root node
  const ast = {
    type: 'Program',
    body: [],
    sourceType: 'script'
  };
  
  // Add some mock nodes based on program text
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    
    // Try to determine statement type
    if (line.includes('if')) {
      ast.body.push({
        type: 'IfStatement',
        test: {
          type: 'BinaryExpression',
          operator: line.includes('>') ? '>' : line.includes('<') ? '<' : '==',
          left: { type: 'Identifier', name: 'x' },
          right: { type: 'Literal', value: 1 }
        },
        consequent: { type: 'BlockStatement', body: [] },
        alternate: null
      });
    } else if (line.includes('while')) {
      ast.body.push({
        type: 'WhileStatement',
        test: {
          type: 'BinaryExpression',
          operator: line.includes('>') ? '>' : line.includes('<') ? '<' : '==',
          left: { type: 'Identifier', name: 'i' },
          right: { type: 'Literal', value: 10 }
        },
        body: { type: 'BlockStatement', body: [] }
      });
    } else if (line.includes('=')) {
      const parts = line.split('=').map(p => p.trim());
      ast.body.push({
        type: 'AssignmentExpression',
        operator: '=',
        left: { type: 'Identifier', name: parts[0] },
        right: { type: 'Literal', value: 1 }
      });
    } else if (line.includes('assert')) {
      ast.body.push({
        type: 'AssertStatement',
        test: {
          type: 'BinaryExpression',
          operator: '==',
          left: { type: 'Identifier', name: 'result' },
          right: { type: 'Literal', value: 5 }
        }
      });
    }
  }
  
  return ast;
};

// Mock SSA generation
export const generateMockSSA = (program: string): string => {
  const lines = program.split('\n').filter(line => line.trim());
  let ssaCode = '// SSA form of the program\n';
  
  // Keep track of variable versions
  const variables: Record<string, number> = {};
  
  // Process each line and convert to SSA form
  lines.forEach((line, index) => {
    const trimmedLine = line.trim();
    
    // Skip comments and empty lines
    if (trimmedLine.startsWith('//') || !trimmedLine) {
      ssaCode += trimmedLine + '\n';
      return;
    }
    
    if (trimmedLine.includes('=')) {
      // Assignment statement
      const parts = trimmedLine.split('=').map(p => p.trim());
      const varName = parts[0];
      const expr = parts[1];
      
      // Increment the version
      variables[varName] = (variables[varName] || 0) + 1;
      const version = variables[varName];
      
      // Create SSA statement
      ssaCode += `${varName}_${version} = ${expr.replace(/([a-zA-Z_][a-zA-Z0-9_]*)/g, (match) => {
        // Replace variables with their latest version
        if (variables[match]) {
          return `${match}_${variables[match]}`;
        }
        return match;
      })};\n`;
    } else if (trimmedLine.includes('if')) {
      // If statement
      ssaCode += trimmedLine + '\n';
    } else if (trimmedLine.includes('while')) {
      // While loop
      ssaCode += trimmedLine + '\n';
    } else if (trimmedLine.includes('assert')) {
      // Assert statement
      ssaCode += trimmedLine.replace(/([a-zA-Z_][a-zA-Z0-9_]*)/g, (match) => {
        // Replace variables in assert with their latest version
        if (variables[match]) {
          return `${match}_${variables[match]}`;
        }
        return match;
      }) + '\n';
    } else {
      // Other statements pass through
      ssaCode += trimmedLine + '\n';
    }
  });
  
  return ssaCode;
};

// Mock optimized SSA generation
export const generateOptimizedMockSSA = (program: string): string => {
  // Start with basic SSA
  const basicSsa = generateMockSSA(program);
  
  // Add some optimization comments
  let optimizedSsa = '// Optimized SSA form\n';
  optimizedSsa += '// - Dead code eliminated\n';
  optimizedSsa += '// - Constant propagation applied\n';
  optimizedSsa += '// - Common subexpressions eliminated\n\n';
  
  // Add the actual optimized code (simplified for this mock)
  const lines = basicSsa.split('\n');
  
  // Skip headers and add the rest with minor modifications
  for (let i = 3; i < lines.length; i++) {
    const line = lines[i];
    
    // Skip some assignments to simulate optimization
    if (i % 3 === 0 && line.includes('=')) {
      optimizedSsa += '// Eliminated: ' + line + '\n';
      continue;
    }
    
    optimizedSsa += line + '\n';
  }
  
  return optimizedSsa;
};

// Mock SSA AST generation
export const generateMockSSAAST = (program: string): any => {
  // Create an AST representation of the SSA code
  const ssaCode = generateMockSSA(program);
  const lines = ssaCode.split('\n').filter(line => !line.startsWith('//') && line.trim());
  
  // Root node
  const ast = {
    type: 'SSAProgram',
    body: [],
    sourceType: 'ssa'
  };
  
  // Add nodes based on SSA code
  lines.forEach(line => {
    const trimmedLine = line.trim();
    
    if (trimmedLine.includes('=')) {
      // SSA Assignment
      const parts = trimmedLine.split('=').map(p => p.trim());
      ast.body.push({
        type: 'SSAAssignment',
        target: parts[0],
        value: parts[1].replace(';', ''),
        original: trimmedLine
      });
    } else if (trimmedLine.includes('if')) {
      // If statement in SSA
      ast.body.push({
        type: 'SSAIfStatement',
        condition: trimmedLine.replace('if', '').replace('(', '').replace(')', '').trim(),
        original: trimmedLine
      });
    } else if (trimmedLine.includes('while')) {
      // While loop in SSA
      ast.body.push({
        type: 'SSAWhileStatement',
        condition: trimmedLine.replace('while', '').replace('(', '').replace(')', '').trim(),
        original: trimmedLine
      });
    } else if (trimmedLine.includes('assert')) {
      // Assert in SSA
      ast.body.push({
        type: 'SSAAssertStatement',
        condition: trimmedLine.replace('assert', '').replace('(', '').replace(')', '').trim(),
        original: trimmedLine
      });
    } else if (trimmedLine.includes('{') || trimmedLine.includes('}')) {
      // Block markers
      ast.body.push({
        type: 'SSABlockMarker',
        marker: trimmedLine,
        original: trimmedLine
      });
    }
  });
  
  return ast;
};
