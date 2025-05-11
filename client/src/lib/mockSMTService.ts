/**
 * Mock SMT Service
 * Provides mock SMT constraint generation for development and testing
 */

/**
 * Generate SMT constraints from program code
 * @param program Program code to generate constraints for
 * @param isEquivalence Whether this is an equivalence check
 * @param secondProgram Optional second program for equivalence checking
 * @returns Generated SMT constraints
 */
export const generateMockSMTConstraints = async (
  program: string,
  isEquivalence: boolean = false,
  secondProgram?: string
): Promise<string> => {
  try {
    // Attempt to generate meaningful constraints based on content
    const constraints = isEquivalence 
      ? generateEquivalenceConstraints(program, secondProgram || '')
      : generateVerificationConstraints(program);
    
    return constraints;
  } catch (error) {
    console.error('Error generating mock SMT constraints:', error);
    return `; Error generating SMT constraints: ${error instanceof Error ? error.message : String(error)}`;
  }
};

/**
 * Generate verification constraints for a single program
 */
function generateVerificationConstraints(program: string): string {
  // Extract variable names with a simple regex
  const variables = (program.match(/\b([a-zA-Z_][a-zA-Z0-9_]*)\s*:=/g) || [])
    .map(match => match.replace(/\s*:=$/, ''))
    .filter((v, i, self) => self.indexOf(v) === i);
  
  // Add some default variables if none found
  if (variables.length === 0) {
    variables.push('x', 'y', 'result');
  }
  
  // Check for assertions
  const hasAssertions = program.includes('assert');
  
  // Generate SMT-LIB format constraints
  let smt = `; SMT constraints for verification\n`;
  smt += `; Generated from program\n\n`;
  
  // Add variable declarations
  smt += `; Variable declarations\n`;
  variables.forEach((variable) => {
    smt += `(declare-const ${variable}_0 Int)\n`;
    
    // Add more versions for variables that appear multiple times
    if (countOccurrences(program, variable) > 1) {
      smt += `(declare-const ${variable}_1 Int)\n`;
    }
  });
  
  smt += `\n; Path constraints\n`;
  
  // Add some basic constraints
  if (variables.length > 0) {
    // Initial values
    smt += `(assert (= ${variables[0]}_0 0))\n`;
    
    if (variables.length > 1) {
      smt += `(assert (= ${variables[1]}_0 0))\n`;
    }
    
    // Add constraints based on program contents
    if (program.includes('while') || program.includes('for')) {
      smt += `\n; Loop constraints\n`;
      smt += `(assert (< ${variables[0]}_0 10))\n`;
      
      if (variables.length > 1) {
        smt += `(assert (= ${variables[1]}_1 (+ ${variables[1]}_0 ${variables[0]}_0)))\n`;
      }
    }
    
    if (program.includes('if')) {
      smt += `\n; Conditional constraints\n`;
      smt += `(assert (> ${variables[0]}_0 0))\n`;
      smt += `(assert (ite (> ${variables[0]}_0 5) (= ${variables[1]}_1 1) (= ${variables[1]}_1 0)))\n`;
    }
    
    // Add negated assertions if found
    if (hasAssertions) {
      smt += `\n; Assertion constraints (negated to find counterexamples)\n`;
      
      if (program.includes('>') || program.includes('<')) {
        // Look for inequality assertions
        if (program.includes('>=')) {
          smt += `(assert (not (>= ${variables[0]}_0 0)))\n`;
        } else if (program.includes('<=')) {
          smt += `(assert (not (<= ${variables[0]}_0 100)))\n`;
        } else if (program.includes('>')) {
          smt += `(assert (not (> ${variables[0]}_0 0)))\n`;
        } else if (program.includes('<')) {
          smt += `(assert (not (< ${variables[0]}_0 100)))\n`;
        }
      } else {
        // Default to equality assertion
        smt += `(assert (not (= ${variables[0]}_0 ${variables.length > 1 ? variables[1] + '_0' : '0'})))\n`;
      }
    }
  }
  
  // Add checking and model generation commands
  smt += `\n; Model generation\n`;
  smt += `(check-sat)\n`;
  smt += `(get-model)\n`;
  
  return smt;
}

/**
 * Generate equivalence constraints for two programs
 */
function generateEquivalenceConstraints(program1: string, program2: string): string {
  // Extract variable names with a simple regex from both programs
  const vars1 = (program1.match(/\b([a-zA-Z_][a-zA-Z0-9_]*)\s*:=/g) || [])
    .map(match => match.replace(/\s*:=$/, ''))
    .filter((v, i, self) => self.indexOf(v) === i);
  
  const vars2 = (program2.match(/\b([a-zA-Z_][a-zA-Z0-9_]*)\s*:=/g) || [])
    .map(match => match.replace(/\s*:=$/, ''))
    .filter((v, i, self) => self.indexOf(v) === i);
  
  // Generate SMT constraints
  let smt = `; SMT constraints for equivalence checking\n`;
  smt += `; Comparing two programs\n\n`;
  
  // Declare variables for both programs (with prefixes to avoid name collisions)
  smt += `; Program 1 variable declarations\n`;
  vars1.forEach((v) => {
    smt += `(declare-const p1_${v}_0 Int)\n`;
  });
  
  smt += `\n; Program 2 variable declarations\n`;
  vars2.forEach((v) => {
    smt += `(declare-const p2_${v}_0 Int)\n`;
  });
  
  // Add input variable declarations (shared between programs)
  smt += `\n; Input variables\n`;
  smt += `(declare-const input_x Int)\n`;
  smt += `(declare-const input_y Int)\n`;
  
  // Add constraints for program 1
  smt += `\n; Program 1 constraints\n`;
  if (vars1.length > 0) {
    // Connect input variables to program variables
    smt += `(assert (= p1_${vars1[0]}_0 input_x))\n`;
    
    if (vars1.length > 1) {
      smt += `(assert (= p1_${vars1[1]}_0 input_y))\n`;
    }
    
    // Add constraints based on program contents
    if (program1.includes('while') || program1.includes('for')) {
      smt += `\n; Program 1 loop constraints\n`;
      const loopVar = vars1.find(v => program1.includes(`${v} :=`));
      if (loopVar) {
        smt += `(assert (= p1_${loopVar}_1 (+ p1_${loopVar}_0 1)))\n`;
      }
    }
  }
  
  // Add constraints for program 2
  smt += `\n; Program 2 constraints\n`;
  if (vars2.length > 0) {
    // Connect input variables to program variables
    smt += `(assert (= p2_${vars2[0]}_0 input_x))\n`;
    
    if (vars2.length > 1) {
      smt += `(assert (= p2_${vars2[1]}_0 input_y))\n`;
    }
    
    // Add constraints based on program contents
    if (program2.includes('while') || program2.includes('for')) {
      smt += `\n; Program 2 loop constraints\n`;
      const loopVar = vars2.find(v => program2.includes(`${v} :=`));
      if (loopVar) {
        smt += `(assert (= p2_${loopVar}_1 (+ p2_${loopVar}_0 1)))\n`;
      }
    }
  }
  
  // Define output variables for both programs
  smt += `\n; Output variables\n`;
  const output1 = vars1.length > 0 ? `p1_${vars1[vars1.length - 1]}_0` : 'p1_result_0';
  const output2 = vars2.length > 0 ? `p2_${vars2[vars2.length - 1]}_0` : 'p2_result_0';
  
  // Check for inequality (to find counterexamples)
  smt += `\n; Equivalence assertion (negated to find counterexamples)\n`;
  smt += `(assert (not (= ${output1} ${output2})))\n`;
  
  // Add checking and model generation commands
  smt += `\n; Model generation\n`;
  smt += `(check-sat)\n`;
  smt += `(get-model)\n`;
  
  return smt;
}

/**
 * Count occurrences of a substring in a string
 */
function countOccurrences(str: string, subStr: string): number {
  return (str.match(new RegExp(`\\b${subStr}\\b`, 'g')) || []).length;
}
