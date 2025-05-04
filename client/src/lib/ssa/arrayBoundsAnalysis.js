/**
 * Array Bounds Analysis
 * 
 * Analyzes array access operations to detect potential out-of-bounds accesses
 * and inserts runtime checks or static verifications.
 */

/**
 * Analyzes array accesses in the SSA form and inserts bounds checks
 * @param {Object} ssaProgram - The SSA program to analyze
 * @param {Object} options - Analysis options
 * @returns {Object} The SSA program with bounds checks inserted
 */
export function analyzeArrayBounds(ssaProgram, options = {}) {
  const config = {
    insertRuntimeChecks: true,
    generateAssertions: true,
    trackArraySizes: true,
    ...options
  };
  
  if (!ssaProgram || !ssaProgram.blocks) {
    return ssaProgram;
  }
  
  // Create a new copy of the program
  const analyzedProgram = JSON.parse(JSON.stringify(ssaProgram));
  
  // Track array declarations and their known sizes
  const arrayInfo = collectArrayInfo(analyzedProgram);
  
  // Process each block and insert bounds checks
  for (const block of analyzedProgram.blocks) {
    if (!block || !block.instructions) continue;
    
    const newInstructions = [];
    
    for (const instr of block.instructions) {
      // Keep the original instruction
      newInstructions.push(instr);
      
      if (!instr) continue;
      
      // Check for array accesses
      if (instr.type === 'Assignment') {
        // Check target for array access (array[i] := value)
        if (instr.target && instr.target.type === 'ArrayAccess') {
          const boundsCheck = generateBoundsCheck(
            instr.target.array, 
            instr.target.index, 
            arrayInfo, 
            config
          );
          if (boundsCheck) {
            newInstructions.push(boundsCheck);
          }
        }
        
        // Check value for array accesses (x := array[i])
        if (instr.value && instr.value.type === 'ArrayAccess') {
          const boundsCheck = generateBoundsCheck(
            instr.value.array, 
            instr.value.index, 
            arrayInfo, 
            config
          );
          if (boundsCheck) {
            // Insert the bounds check before the instruction
            newInstructions.splice(newInstructions.length - 1, 0, boundsCheck);
          }
        }
      }
      
      // Track array initializations and updates
      updateArrayInfo(instr, arrayInfo);
    }
    
    // Update the block with new instructions
    block.instructions = newInstructions;
  }
  
  // Add array info to program metadata
  analyzedProgram.metadata = {
    ...analyzedProgram.metadata,
    arrayBoundsAnalysis: {
      performed: true,
      arrays: Object.fromEntries(arrayInfo)
    }
  };
  
  return analyzedProgram;
}

/**
 * Collect information about arrays declared in the program
 * @param {Object} program - The SSA program
 * @returns {Map} Map of array names to their information
 */
function collectArrayInfo(program) {
  const arrayInfo = new Map();
  
  // Look for array declarations in variable initializations
  for (const block of program.blocks || []) {
    for (const instr of block.instructions || []) {
      // Skip non-assignment instructions
      if (!instr || instr.type !== 'Assignment') continue;
      
      // Check for array initializations
      if (instr.value && instr.value.type === 'ArrayLiteral') {
        arrayInfo.set(instr.target, {
          name: instr.target,
          knownSize: instr.value.elements.length,
          constantSize: true,
          accessPatterns: []
        });
      }
      
      // Check for array creation operations
      if (instr.value && instr.value.type === 'NewArray') {
        const sizeExpr = instr.value.size;
        let knownSize = null;
        let constantSize = false;
        
        // Try to determine if size is a constant
        if (sizeExpr.type === 'IntegerLiteral') {
          knownSize = sizeExpr.value;
          constantSize = true;
        }
        
        arrayInfo.set(instr.target, {
          name: instr.target,
          knownSize,
          constantSize,
          accessPatterns: []
        });
      }
    }
  }
  
  return arrayInfo;
}

/**
 * Update array information based on an instruction
 * @param {Object} instr - The instruction to analyze
 * @param {Map} arrayInfo - Map of array information
 */
function updateArrayInfo(instr, arrayInfo) {
  // Skip non-assignment instructions
  if (!instr || instr.type !== 'Assignment') return;
  
  // Record array access patterns
  if (instr.value && instr.value.type === 'ArrayAccess') {
    const arrayName = instr.value.array.name;
    const indexExpr = instr.value.index;
    
    if (arrayInfo.has(arrayName)) {
      const info = arrayInfo.get(arrayName);
      info.accessPatterns.push({
        index: indexExpr,
        location: instr.location,
        instruction: 'read'
      });
    }
  }
  
  if (instr.target && instr.target.type === 'ArrayAccess') {
    const arrayName = instr.target.array.name;
    const indexExpr = instr.target.index;
    
    if (arrayInfo.has(arrayName)) {
      const info = arrayInfo.get(arrayName);
      info.accessPatterns.push({
        index: indexExpr,
        location: instr.location,
        instruction: 'write'
      });
    }
  }
}

/**
 * Generate bounds check for an array access
 * @param {Object} arrayExpr - The array expression
 * @param {Object} indexExpr - The index expression
 * @param {Map} arrayInfo - Map of array information
 * @param {Object} config - Configuration options
 * @returns {Object|null} The bounds check assertion or null
 */
function generateBoundsCheck(arrayExpr, indexExpr, arrayInfo, config) {
  if (!arrayExpr || !indexExpr) return null;
  
  // Only handle simple array variables for now
  if (arrayExpr.type !== 'Variable') return null;
  
  const arrayName = arrayExpr.name;
  
  // Lookup array info
  if (!arrayInfo.has(arrayName)) return null;
  const info = arrayInfo.get(arrayName);
  
  // Create a runtime assertion for the bounds check
  if (config.insertRuntimeChecks || config.generateAssertions) {
    return {
      type: 'Assert',
      condition: {
        type: 'BinaryExpression',
        left: {
          type: 'BinaryExpression',
          left: indexExpr,
          operator: '>=',
          right: { type: 'IntegerLiteral', value: 0 }
        },
        operator: '&&',
        right: {
          type: 'BinaryExpression',
          left: indexExpr,
          operator: '<',
          right: info.constantSize ? 
            { type: 'IntegerLiteral', value: info.knownSize } :
            { type: 'ArrayLength', array: arrayExpr }
        }
      },
      message: `Array index out of bounds: ${arrayName}`,
      metadata: {
        type: 'boundsCheck',
        array: arrayName,
        index: JSON.parse(JSON.stringify(indexExpr))
      }
    };
  }
  
  return null;
}
