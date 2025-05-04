/**
 * Debug utility for SSA transformation
 */

import { parseProgram } from '../parser/index.js';
import { transformToSSA } from '../ssa/index.js';

// Simple test program
const testProgram = `
  x := 5;
  y := x + 3;
  z := y * 2;
`;

/**
 * Inspect object structure
 */
function inspectObject(obj, maxDepth = 3, depth = 0) {
  if (depth > maxDepth) return '... (max depth reached)';
  
  if (obj === null) return 'null';
  if (obj === undefined) return 'undefined';
  
  if (typeof obj !== 'object') return String(obj);
  
  if (Array.isArray(obj)) {
    if (obj.length === 0) return '[]';
    
    const items = obj
      .slice(0, 5)
      .map(item => inspectObject(item, maxDepth, depth + 1))
      .join(', ');
      
    return `[${items}${obj.length > 5 ? ', ...' : ''}]`;
  }
  
  const entries = Object.entries(obj)
    .slice(0, 10)
    .map(([key, value]) => `${key}: ${inspectObject(value, maxDepth, depth + 1)}`)
    .join(', ');
    
  return `{ ${entries}${Object.keys(obj).length > 10 ? ', ...' : ''} }`;
}

/**
 * Create a minimal SSA structure for empty or invalid SSA programs
 */
function createMinimalSSA(ast) {
  console.log('Creating minimal SSA structure from AST');
  
  // Extract variable names from the AST if possible
  const variables = new Set();
  try {
    if (ast && ast.statements) {
      ast.statements.forEach(stmt => {
        if (stmt.type === 'Assignment' && stmt.target) {
          variables.add(stmt.target.name || 'unknown');
        }
      });
    }
  } catch (error) {
    console.warn('Error extracting variables from AST:', error.message);
  }
  
  // Create a minimal basic block
  const mainBlock = {
    label: 'entry',
    instructions: Array.from(variables).map(varName => ({
      type: 'Assignment',
      target: varName,
      value: { type: 'IntegerLiteral', value: 0 }
    })),
    terminator: {
      type: 'Jump',
      target: 'exit'
    }
  };
  
  const exitBlock = {
    label: 'exit',
    instructions: [],
    terminator: null
  };
  
  // Return minimal valid SSA structure
  return {
    blocks: [mainBlock, exitBlock],
    entryBlock: 'entry',
    exitBlock: 'exit',
    metadata: {
      synthetic: true,
      message: 'Generated fallback SSA structure'
    }
  };
}

/**
 * Debug SSA transformation
 */
async function debugSSA() {
  console.log('========================================');
  console.log('Debugging SSA Transformation');
  console.log('========================================');
  
  try {
    console.log('Parsing test program:');
    console.log(testProgram);
    
    const ast = parseProgram(testProgram);
    console.log('\nAST structure:');
    console.log(inspectObject(ast, 2));
    
    // Inspect transformToSSA function
    console.log('\nInspecting transformToSSA function:');
    console.log('transformToSSA is a', typeof transformToSSA);
    
    console.log('\nTransforming to SSA:');
    const ssaProgram = transformToSSA(ast);
    
    console.log('\nSSA Program structure:');
    console.log(inspectObject(ssaProgram, 1));
    
    // Check if SSA is valid and create minimal structure if not
    let workingSSA = ssaProgram;
    if (!ssaProgram || !ssaProgram.blocks || !Array.isArray(ssaProgram.blocks)) {
      console.log('\nSSA program is invalid or empty. Creating minimal structure.');
      workingSSA = createMinimalSSA(ast);
      console.log('Created minimal SSA:', inspectObject(workingSSA, 2));
    }
    
    console.log('\nBlocks available:');
    if (!workingSSA.blocks) {
      console.log('No blocks array in SSA program');
    } else {
      console.log(`Number of blocks: ${workingSSA.blocks.length}`);
      
      for (let i = 0; i < workingSSA.blocks.length; i++) {
        const block = workingSSA.blocks[i];
        console.log(`\nBlock ${i}:`);
        console.log(`- Label: ${block.label}`);
        console.log(`- Instructions: ${block.instructions?.length || 0}`);
        
        if (block.instructions && block.instructions.length > 0) {
          console.log('- First instruction:', inspectObject(block.instructions[0], 2));
        }
        
        console.log(`- Phi functions: ${block.phiFunctions?.length || 0}`);
        console.log(`- Terminator: ${block.terminator?.type || 'none'}`);
      }
    }
    
    console.log('\n========================================');
    console.log('Debug completed');
    console.log('========================================');
    
  } catch (error) {
    console.error('Error during debugging:', error);
  }
}

// Run debug function
debugSSA().catch(console.error);
