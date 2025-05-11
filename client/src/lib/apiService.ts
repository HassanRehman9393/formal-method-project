/**
 * API Service
 * Central service for all API interactions with the backend
 */
import { apiRequest, API_BASE_URL, handleApiError, ApiResponse } from '../utils/apiUtils';
import axios from 'axios';

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

export interface VerificationResult {
  verified: boolean;
  counterexamples?: Array<{ [key: string]: any }>;
  success: boolean;
  error?: string;
}

export interface EquivalenceResult {
  equivalent: boolean;
  counterexample?: { [key: string]: any };
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

/**
 * Parse a program into an AST
 */
export const parseProgram = async (program: string): Promise<ParseResult> => {
  try {
    console.log('Parsing program:', program);
    const response = await apiRequest<{ ast: any }>('/parse', 'POST', { programCode: program });
    console.log('Parse result from API:', response);
    
    // The API is returning the AST directly in the response.ast instead of in response.data.ast
    if (response.success && response.ast) {
      // Handle case where ast is directly in the response
      return {
        ast: response.ast,
        success: true,
        error: undefined
      };
    } else if (response.success && response.data?.ast) {
      // Handle case where ast is in response.data.ast
      return {
        ast: response.data.ast,
        success: true,
        error: undefined
      };
    } else {
      // Handle error case
      return {
        ast: null,
        success: false,
        error: response.message || 'Failed to parse program'
      };
    }
  } catch (error) {
    console.error('Error in parseProgram:', error);
    return {
      ast: null,
      success: false,
      error: error instanceof Error ? error.message : 'Unknown error parsing program'
    };
  }
};

/**
 * Transform a program or AST to SSA form
 */
export const transformToSSA = async (
  program: string | object,
  options: { loopUnrollingDepth: number } = { loopUnrollingDepth: 5 }
): Promise<SSATransformResult> => {
  try {
    // Check if we have a valid program input
    if (program === undefined || program === null) {
      console.error('Invalid input to transformToSSA: program is null or undefined');
      return {
        ssaAst: null,
        ssaCode: '',
        optimizedSsaCode: '',
        success: false,
        error: 'Invalid input: No program or AST provided'
      };
    }
    
    // If program is an object (AST), ensure it's a valid AST 
    if (typeof program === 'object') {
      // Add some validation to ensure it's an AST
      const astObj = program as any;
      if (!astObj.type || !astObj.body) {
        console.error('Invalid AST object:', astObj);
        return {
          ssaAst: null,
          ssaCode: '',
          optimizedSsaCode: '',
          success: false,
          error: 'Invalid AST object: Missing required properties (type, body)'
        };
      }
    }
    
    // Ensure we're using the proper parameter name
    // Server expects programCode (if string) or ast (if object)
    const payload = typeof program === 'string'
      ? { programCode: program, loopUnrollingDepth: options.loopUnrollingDepth }
      : { ast: program, loopUnrollingDepth: options.loopUnrollingDepth };
    
    console.log('SSA Transform Payload:', typeof payload.ast === 'object' 
      ? 'AST object provided' 
      : `Program code (${payload.programCode?.substring(0, 30)}...)`);
      
    // Make the request
    const response = await axios.post<ApiResponse<{
      ssaAst: any;
      ssaCode: string;
      optimizedSsaCode: string;
    }>>(`${API_BASE_URL}/parse/transform-ssa`, payload);

    console.log('SSA Transform Response status:', response.status);
    
    // Check if the response is successful
    if (response.data.success) {
      console.log('SSA Transform Response successful');
      
      // Extract data - try both formats
      const data = response.data.data || response.data;
      
      // Extract fields from appropriate location
      const ssaAst = data.ssaAst || data.ssaAST;
      const ssaCode = data.ssaCode || '';
      const optimizedSsaCode = data.optimizedSsaCode || data.optimizedSSACode || '';
      
      if (!ssaAst) {
        console.warn('SSA transformation successful but no SSA AST returned:', data);
      }
      
      return {
        ssaAst,
        ssaCode,
        optimizedSsaCode,
        success: true,
        error: null
      };
    } else {
      // Handle error response
      const errorMsg = response.data.message || response.data.error || 'SSA transformation failed';
      console.error('SSA transformation error:', errorMsg);
      return {
        ssaAst: null,
        ssaCode: '',
        optimizedSsaCode: '',
        success: false,
        error: errorMsg
      };
    }
  } catch (error) {
    console.error('Error in transformToSSA:', error);
    let errorMessage = 'SSA transformation failed';
    
    if (axios.isAxiosError(error) && error.response) {
      // If we received a response with error data
      const responseData = error.response.data;
      errorMessage = responseData.message || responseData.error || `SSA transformation failed (${error.response.status})`;
      console.error('API error response:', responseData);
    } else if (error instanceof Error) {
      errorMessage = error.message;
    }
    
    return {
      ssaAst: null,
      ssaCode: '',
      optimizedSsaCode: '',
      success: false,
      error: errorMessage
    };
  }
};

/**
 * Verify a program using the server's verification endpoint
 */
export async function verifyProgram(
  program: string,
  options?: VerificationOptions
): Promise<VerificationResult> {
  try {
    console.log('Making verification request with program:', program?.substring(0, 30) + '...');
    console.log('Verification options:', options);
    
    // Define the possible endpoints to try in order
    const endpoints = [
      `${API_BASE_URL}/verify/verify`,  // This is the correct endpoint based on server routes
      `${API_BASE_URL}/verify`,         // Fallback to the base verify endpoint
      `${API_BASE_URL}/verify/program`  // Another possible endpoint
    ];
    
    // Define the possible payload formats to try
    const payloadFormats = [
      { program, options },
      { programCode: program, options },
      { code: program, options }
    ];
    
    let lastError: any = null;
    
    // Try each endpoint with each payload format until one succeeds
    for (const endpoint of endpoints) {
      for (const payload of payloadFormats) {
        try {
          console.log(`Trying verification with endpoint ${endpoint} and payload format:`, payload);
          
          const response = await axios.post<ApiResponse<VerificationResult>>(
            endpoint,
            payload
          );
          
          console.log('Verification response status:', response.status, response.statusText);
          console.log('Full verification response:', response.data);
          
          if (response.status === 200) {
            console.log('Verification successful');
            
            // Extract verification result - handle both formats
            const data = response.data.data || response.data;
            
            // Debug what we received
            console.log('Processing verification data:', data);
            
            // Extract the 'verified' field from the response
            // It could be in various locations due to API inconsistency
            let verified = false;
            
            // Try all possible locations for the verified status
            if (data?.verified !== undefined) {
              verified = Boolean(data.verified);
            } else if (data?.valid !== undefined) {
              verified = Boolean(data.valid);
            } else if (data?.result?.verified !== undefined) {
              verified = Boolean(data.result.verified);
            } else if (data?.result?.valid !== undefined) {
              verified = Boolean(data.result.valid);
            } else if (data?.data?.verified !== undefined) {
              verified = Boolean(data.data.verified);
            } 
            
            console.log('Extracted verified status:', verified);
            
            // Extract counterexamples - could be in multiple locations
            let counterexamples = [];
            
            if (data?.counterexamples) {
              counterexamples = data.counterexamples;
            } else if (data?.models) {
              counterexamples = data.models;
            } else if (data?.model) {
              counterexamples = [data.model];
            } else if (data?.data?.counterexamples) {
              counterexamples = data.data.counterexamples;
            } else if (data?.result?.counterexamples) {
              counterexamples = data.result.counterexamples;
            }
            
            console.log('Extracted counterexamples:', counterexamples);
            
            // Return standardized verification result
            return { 
              success: true, 
              verified, 
              counterexamples
            };
          }
        } catch (error) {
          console.error(`Error with endpoint ${endpoint}:`, error);
          lastError = error;
          // Continue trying other endpoints/formats
        }
      }
    }
    
    // If we reach here, none of the endpoint combinations worked
    throw lastError || new Error('Failed to verify program with all available endpoints');
  } catch (error: any) {
    console.error('Verification error:', error);
    return {
      success: false,
      verified: false,
      error: error.message || 'Unknown error occurred during verification'
    };
  }
}

/**
 * Check equivalence between two programs
 */
export async function checkEquivalence(
  program1: string,
  program2: string,
  options?: VerificationOptions
): Promise<EquivalenceResult> {
  try {
    console.log('Making equivalence check request...');
    console.log('Programs to compare (snippets):', 
      program1?.substring(0, 30) + '...', 
      program2?.substring(0, 30) + '...');
    
    // Define the possible endpoints to try in order
    const endpoints = [
      `${API_BASE_URL}/equivalence`,
      `${API_BASE_URL}/equivalence/check`,
      `${API_BASE_URL}/verify/equivalence`
    ];
    
    // Define the possible payload formats to try
    const payloadFormats = [
      { program1, program2, options },
      { programCode1: program1, programCode2: program2, options },
      { program: program1, secondProgram: program2, options }
    ];
    
    let lastError: any = null;
    
    // Try each endpoint with each payload format until one succeeds
    for (const endpoint of endpoints) {
      for (const payload of payloadFormats) {
        try {
          console.log(`Trying equivalence check with endpoint ${endpoint} and payload format:`, payload);
          
          const response = await axios.post<ApiResponse<EquivalenceResult>>(
            endpoint,
            payload
          );
          
          console.log('Equivalence response status:', response.status, response.statusText);
          
          if (response.data.success) {
            console.log('Equivalence check successful');
            
            // Extract equivalence result - handle both formats
            const data = response.data.data || response.data;
            
            return {
              // Look for the equivalent field in both locations
              equivalent: data.equivalent !== undefined ? data.equivalent : false,
              // Extract counterexample from either property
              counterexample: data.counterexample || null,
              success: true,
              error: null
            };
          } else {
            console.warn('Endpoint responded with error:', response.data.message || response.data.error);
            lastError = response.data.message || response.data.error || 'Equivalence check failed';
          }
        } catch (error) {
          if (axios.isAxiosError(error) && error.response?.status === 404) {
            console.warn(`Endpoint ${endpoint} not found, trying next option`);
            lastError = error;
            continue;
          } else {
            console.error('Error during equivalence check request:', error);
            lastError = error;
          }
        }
      }
    }
    
    // If we've tried all options and none worked, return an error result
    if (lastError) {
      console.error('All equivalence check attempts failed');
      if (axios.isAxiosError(lastError) && lastError.response) {
        return {
          equivalent: false,
          success: false,
          error: lastError.response.data?.message || lastError.response.data?.error || 'Equivalence check failed',
          counterexample: null
        };
      } else {
        return {
          equivalent: false,
          success: false,
          error: lastError instanceof Error ? lastError.message : String(lastError),
          counterexample: null
        };
      }
    }
    
    // Shouldn't reach here, but just in case
    return {
      equivalent: false,
      success: false,
      error: 'Could not check equivalence - all attempts failed',
      counterexample: null
    };
  } catch (error) {
    handleApiError(error);
    return {
      equivalent: false,
      success: false,
      error: error instanceof Error ? error.message : 'An unknown error occurred',
      counterexample: null
    };
  }
}

/**
 * Generate SMT constraints for a program
 */
export async function generateSMTConstraints(
  program: string,
  mode: 'verify' | 'equivalence' = 'verify',
  secondProgram?: string
): Promise<SMTConstraintsResult> {
  try {
    // Determine the endpoint based on whether it's for equivalence or verification
    const endpoint = mode === 'equivalence' 
      ? `${API_BASE_URL}/equivalence/generate-smt` 
      : `${API_BASE_URL}/verify/generate-smt`;
    
    console.log(`Generating SMT constraints using endpoint: ${endpoint}`);
    
    const payload = mode === 'equivalence'
      ? { program, secondProgram, options: {} }
      : { program, options: {} };
    
    console.log('SMT generation payload:', payload);
    
    // Make a direct axios request with detailed logging
    const response = await axios.post<any>(
      endpoint,
      payload,
      {
        headers: {
          'Content-Type': 'application/json',
          'Accept': 'application/json'
        }
      }
    );
    
    console.log('SMT generation raw response status:', response.status, response.statusText);
    
    // Log the raw response data for debugging
    console.log('SMT response data type:', typeof response.data);
    if (typeof response.data === 'object') {
      console.log('SMT response keys:', Object.keys(response.data));
    }
    
    // Safely extract and convert SMT constraints with extensive validation
    let smtConstraints = '';
    let success = false;
    let errorMessage = null;
    
    // First check if we received any data
    if (response.data) {
      success = response.data.success === true;
      
      // Extract constraints with multiple fallbacks
      try {
        // Try all possible locations where constraints might be
        if (response.data?.data?.smtConstraints !== undefined) {
          const raw = response.data.data.smtConstraints;
          smtConstraints = typeof raw === 'string' ? raw : JSON.stringify(raw);
        } else if (response.data?.data?.smtScript !== undefined) {
          const raw = response.data.data.smtScript;
          smtConstraints = typeof raw === 'string' ? raw : JSON.stringify(raw);
        } else if (response.data?.smtConstraints !== undefined) {
          const raw = response.data.smtConstraints;
          smtConstraints = typeof raw === 'string' ? raw : JSON.stringify(raw);
        } else if (response.data?.smtScript !== undefined) {
          const raw = response.data.smtScript;
          smtConstraints = typeof raw === 'string' ? raw : JSON.stringify(raw);
        } else if (response.data?.data !== undefined) {
          // If data is a string, use it directly
          if (typeof response.data.data === 'string') {
            smtConstraints = response.data.data;
          } 
          // If data is an object that might have SMT constraints
          else if (typeof response.data.data === 'object' && response.data.data !== null) {
            // Look for success and result properties inside data
            if (response.data.data.success && response.data.data.result) {
              const raw = response.data.data.result;
              smtConstraints = typeof raw === 'string' ? raw : JSON.stringify(raw);
            } else if (response.data.data.smtConstraints || response.data.data.smtScript) {
              const raw = response.data.data.smtConstraints || response.data.data.smtScript;
              smtConstraints = typeof raw === 'string' ? raw : JSON.stringify(raw);
            } else {
              // Just stringify the whole data object
              smtConstraints = JSON.stringify(response.data.data);
            }
          }
        } else if (typeof response.data === 'string') {
          // If the entire response is a string, use it
          smtConstraints = response.data;
        } else {
          // Last resort: stringify the entire response
          smtConstraints = JSON.stringify(response.data);
        }
      } catch (e) {
        console.error('Error extracting SMT constraints:', e);
        errorMessage = e instanceof Error ? e.message : 'Error extracting SMT constraints';
        smtConstraints = '';
      }
      
      // Final safety check for smtConstraints
      if (smtConstraints === undefined || smtConstraints === null) {
        console.warn('SMT constraints is null or undefined, using empty string');
        smtConstraints = '';
      }
      
      // Log what we extracted
      console.log('Extracted SMT constraints (type):', typeof smtConstraints);
      console.log('Constraints length:', smtConstraints.length);
      
      // If we have constraints but success wasn't explicitly true, assume success
      if (smtConstraints && smtConstraints.length > 0 && !success) {
        console.log('Setting success to true based on constraints presence');
        success = true;
      }
      
      // Extract error message if present
      if (!success || !smtConstraints) {
        errorMessage = response.data.message || response.data.error || 
                      'Failed to generate valid SMT constraints';
      }
    } else {
      success = false;
      errorMessage = 'No data received from server';
    }
    
    return {
      smtConstraints: smtConstraints || '',
      success,
      error: errorMessage
    };
  } catch (error) {
    handleApiError(error);
    
    if (axios.isAxiosError(error) && error.response) {
      console.log('Error response:', error.response.status, error.response.data);
      return {
        smtConstraints: '',
        success: false,
        error: error.response.data?.message || error.response.data?.error || error.message
      };
    }
    
    return {
      smtConstraints: '',
      success: false,
      error: error instanceof Error ? error.message : String(error)
    };
  }
}
