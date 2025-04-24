/**
 * SSA Visualization Module
 * 
 * Helps visualize SSA form in a readable format
 */

/**
 * Generate HTML representation of SSA code with syntax highlighting
 * @param {string} ssaCode - The SSA code as text
 * @returns {string} HTML with syntax highlighting
 */
export function generateSSAHTML(ssaCode) {
  if (!ssaCode) {
    return '<span class="ssa-error">No SSA code available</span>';
  }
  
  // Simple syntax highlighting
  return ssaCode
    .replace(/φ\((.*?)\)/g, '<span class="ssa-phi">φ($1)</span>')
    .replace(/([a-zA-Z_][a-zA-Z0-9_]*_\d+)/g, '<span class="ssa-var">$1</span>')
    .replace(/(goto|if|else|assert|return)/g, '<span class="ssa-keyword">$1</span>')
    .replace(/([LB][0-9]+):/g, '<span class="ssa-label">$1:</span>')
    .replace(/(\/\/ .*?)$/gm, '<span class="ssa-comment">$1</span>')
    .replace(/\n/g, '<br>');
}

/**
 * Format SSA code for better readability
 * @param {string} ssaCode - The SSA code as text
 * @returns {string} Formatted SSA code
 */
export function formatSSAReadable(ssaCode) {
  if (!ssaCode) {
    return 'No SSA code available';
  }
  
  // Add empty lines between blocks for better readability
  return ssaCode.replace(/^([LB][0-9]+:)/gm, '\n$1');
}

/**
 * Generate a simplified representation of SSA form
 * @param {object} ssaProgram - The SSA program object
 * @returns {string} Simplified readable representation
 */
export function simplifySSA(ssaProgram) {
  if (!ssaProgram || !ssaProgram.blocks) {
    return '// Invalid SSA program structure';
  }
  
  let result = '';
  
  // Show simplified blocks with variable assignments
  for (const block of ssaProgram.blocks) {
    if (!block) continue;
    
    result += `// Block ${block.label}\n`;
    
    // Show phi functions if any
    if (block.phiFunctions && block.phiFunctions.length > 0) {
      for (const phi of block.phiFunctions) {
        if (phi) {
          result += `${phi.target} = φ(${phi.sources.join(', ')})\n`;
        }
      }
    }
    
    // Show regular instructions
    if (block.instructions && block.instructions.length > 0) {
      for (const instr of block.instructions) {
        if (!instr) continue;
        
        if (instr.type === 'Assignment') {
          result += `${instr.target} = ${stringifyValue(instr.value)}\n`;
        } else if (instr.type === 'Assert') {
          result += `assert(${stringifyValue(instr.condition)})\n`;
        } else if (instr.type === 'Comment') {
          result += `// ${instr.text}\n`;
        }
      }
    }
    
    // Add block terminator
    if (block.terminator) {
      if (block.terminator.type === 'Jump') {
        result += `goto ${block.terminator.target}\n`;
      } else if (block.terminator.type === 'Branch') {
        result += `if (${stringifyValue(block.terminator.condition)}) goto ${block.terminator.thenTarget} else goto ${block.terminator.elseTarget}\n`;
      } else if (block.terminator.type === 'Return') {
        result += `return ${stringifyValue(block.terminator.value)}\n`;
      }
    }
    
    result += '\n';
  }
  
  return result;
}

/**
 * Helper function to stringify SSA values
 * @param {*} value - Value to stringify
 * @returns {string} String representation
 */
function stringifyValue(value) {
  if (value === null || value === undefined) {
    return 'undefined';
  }
  
  if (typeof value === 'string' || typeof value === 'number' || typeof value === 'boolean') {
    return String(value);
  }
  
  if (!value || typeof value !== 'object') {
    return 'invalid_value';
  }
  
  try {
    if (value.type === 'BinaryExpression') {
      return `${stringifyValue(value.left)} ${value.operator} ${stringifyValue(value.right)}`;
    }
    
    if (value.type === 'UnaryExpression') {
      return `${value.operator}${stringifyValue(value.operand)}`;
    }
    
    if (value.type === 'ArrayAccess') {
      return `${stringifyValue(value.array)}[${stringifyValue(value.index)}]`;
    }
    
    // Default case
    return `<${value.type || 'unknown'}>`;
  } catch (error) {
    return `error(${error.message})`;
  }
}
