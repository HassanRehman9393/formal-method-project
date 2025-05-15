/**
 * API Service
 * Central service for all API interactions with the backend
 */
import { API_BASE_URL } from '../utils/apiUtils';
import axios from 'axios';
import { 
  VerificationResult, 
  EquivalenceResult, 
  VerificationMode 
} from '../types/verification';

export interface ParseResult {
  ast: any;
  success: boolean;
  error?: string;
}

export interface SSATransformResult {
  ssaAst: any;
  ssaCode: string;
  optimizedSsaCode: string;
  success: boolean;
  error?: string;
}

export interface SMTConstraintsResult {
  smtConstraints: string;
  success: boolean;
  error?: string;
}

export interface VerificationOptions {
  loopUnrollingDepth?: number;
  [key: string]: any;
}

export interface EquivalenceOptions {
  loopUnrollingDepth?: number;
  outputVars?: string[];
  [key: string]: any;
}

// API Endpoints
const PARSE_ENDPOINT = `${API_BASE_URL}/parse`;
const SSA_TRANSFORM_ENDPOINT = `${API_BASE_URL}/parse/transform-ssa`;
const GENERATE_SMT_ENDPOINT = `${API_BASE_URL}/verify/generate-smt`;
const VERIFY_ENDPOINT = `${API_BASE_URL}/verify/verify`;
const EQUIVALENCE_ENDPOINT = `${API_BASE_URL}/equivalence`;

/**
 * Parse program code and return AST
 * @param program Program code
 * @returns AST or error
 */
export const parseProgram = async (program: string): Promise<ParseResult> => {
  try {
    const response = await fetch(PARSE_ENDPOINT, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ programCode: program }),
    });

    if (!response.ok) {
      throw new Error(`HTTP error! status: ${response.status}`);
    }

    return await response.json();
  } catch (error) {
    console.error('Error parsing program:', error);
    throw error;
  }
};

/**
 * Transform AST to SSA form
 * @param ast AST to transform
 * @param options Options including loop unrolling depth
 * @returns SSA transformation result
 */
export const transformToSSA = async (ast: any, options: any = {}): Promise<SSATransformResult> => {
  try {
    console.log('SSA Transform Request Body:', JSON.stringify({ ast, options }).substring(0, 500) + '...');
    console.log('Transforming from AST:', typeof ast);
    
    const response = await fetch(SSA_TRANSFORM_ENDPOINT, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ ast, options }),
    });

    if (!response.ok) {
      throw new Error(`HTTP error! status: ${response.status}`);
    }

    const result = await response.json();
    console.log('SSA Transform Success:', JSON.stringify(result).substring(0, 100) + '...');
      
    // Make sure ssaCode and optimizedSsaCode are strings
    if (result.success) {
      // Handle the case where ssaCode might be an object instead of a string
      const ssaCode = typeof result.ssaCode === 'string' 
        ? result.ssaCode 
        : JSON.stringify(result.ssaCode, null, 2);
      
      // Handle the case where optimizedSsaCode might be an object instead of a string
      const optimizedSsaCode = typeof result.optimizedSsaCode === 'string'
        ? result.optimizedSsaCode
        : JSON.stringify(result.optimizedSsaCode, null, 2);
      
      return {
        ...result,
        ssaCode,
        optimizedSsaCode
      };
    }
    
    return result;
  } catch (error) {
    console.error('Error transforming to SSA:', error);
    throw error;
  }
};

/**
 * Generate SMT constraints from AST
 * @param ast AST to generate constraints for
 * @param options Options including loop unrolling depth
 * @returns SMT constraints or error
 */
export const generateSMT = async (ast: any, options: any = {}): Promise<SMTConstraintsResult> => {
  try {
    const response = await fetch(GENERATE_SMT_ENDPOINT, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ ast, options }),
    });

    if (!response.ok) {
      throw new Error(`HTTP error! status: ${response.status}`);
    }

    return await response.json();
  } catch (error) {
    console.error('Error generating SMT:', error);
    throw error;
  }
};

/**
 * Verify a program
 * @param program Program code
 * @param options Verification options
 * @returns Verification result
 */
export const verifyProgram = async (
  program: string,
  options: any = {}
): Promise<VerificationResult> => {
  try {
    console.log('Sending verify program request:', { program: program.substring(0, 50) + '...', options });
    
    const response = await fetch(VERIFY_ENDPOINT, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ 
        programCode: program, // Primary parameter name
        program,              // Alternative parameter name
        options 
      }),
    });

    if (!response.ok) {
      throw new Error(`HTTP error! status: ${response.status}`);
    }

    const jsonResponse = await response.json();
    console.log('Verify program response:', jsonResponse);
            
    // Handle different response formats
    if (jsonResponse.data) {
      return {
        success: jsonResponse.success,
        verified: jsonResponse.data.verified,
        message: jsonResponse.data.message,
        counterexamples: jsonResponse.data.counterexamples,
        mode: 'verification',
      };
    } else {
            return { 
        success: jsonResponse.success,
        verified: jsonResponse.verified,
        message: jsonResponse.message,
        counterexamples: jsonResponse.counterexamples,
        mode: 'verification',
            };
          }
        } catch (error) {
    console.error('Error verifying program:', error);
    return {
      success: false,
      verified: false,
      error: error instanceof Error ? error.message : 'Unknown error',
      mode: 'verification',
    };
  }
};

/**
 * Check if two programs are equivalent
 * @param program1 First program code
 * @param program2 Second program code
 * @param options Equivalence checking options
 * @returns Equivalence result
 */
export const checkEquivalence = async (
  program1: string,
  program2: string,
  options: any = {}
): Promise<EquivalenceResult> => {
  try {
    const response = await fetch(EQUIVALENCE_ENDPOINT, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ program1, program2, options }),
    });
          
    if (!response.ok) {
      throw new Error(`HTTP error! status: ${response.status}`);
    }

    return await response.json();
  } catch (error) {
    console.error('Error checking equivalence:', error);
    return {
      success: false,
      equivalent: false,
      error: error instanceof Error ? error.message : 'Unknown error',
      mode: 'equivalence',
    };
  }
};

/**
 * Generate SMT constraints for one or two programs
 * @param program1 First program code
 * @param mode Verification mode (verification or equivalence)
 * @param program2 Second program (optional, for equivalence checking)
 * @returns SMT constraints or error
 */
export const generateSMTConstraints = async (
  program1: string,
  mode: VerificationMode = 'verification',
  program2?: string
): Promise<SMTConstraintsResult> => {
  try {
    // Create a consistent payload that matches server expectations
    const payload = {
      programCode: program1, // Primary name the server expects
      program1,              // Alternative name
      mode,                 // Verification mode
    };
    
    // For equivalence checking, add the second program
    if (mode === 'equivalence' && program2) {
      payload['secondProgramCode'] = program2; // Primary name the server expects
      payload['program2'] = program2;          // Alternative name
    }

    console.log('Sending SMT generation request:', payload);

    const response = await fetch(GENERATE_SMT_ENDPOINT, {
      method: 'POST',
        headers: {
          'Content-Type': 'application/json',
      },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      throw new Error(`HTTP error! status: ${response.status}`);
    }

    const result = await response.json();
    
    // Ensure the SMT constraints are a string
    if (result.success) {
      // Handle the case where smtConstraints might be an object instead of a string
      const smtConstraints = typeof result.smtConstraints === 'string'
        ? result.smtConstraints
        : JSON.stringify(result.smtConstraints, null, 2);
        
      return {
        ...result,
        smtConstraints
      };
    }
    
    return result;
  } catch (error) {
    console.error('Error generating SMT constraints:', error);
    return {
      success: false,
      smtConstraints: '',
      error: error instanceof Error ? error.message : 'Unknown error'
    };
  }
};

export default {
  parseProgram,
  transformToSSA,
  generateSMT,
  verifyProgram,
  checkEquivalence,
  generateSMTConstraints,
};
