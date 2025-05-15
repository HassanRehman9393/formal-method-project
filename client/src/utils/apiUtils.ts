// API utility functions for interacting with the backend

import { generateMockSMTConstraints } from '../lib/mockSMTService';

/**
 * Standard API response format
 */
export interface ApiResponse<T> {
  success: boolean;
  data?: T;
  message?: string;
}

// Base API URL - can be configured from environment
export const API_BASE_URL = import.meta.env.VITE_API_BASE_URL || 'http://localhost:3001/api';

// Function to determine if we should use mock data
// During development we can use mock data if the API is not yet available
const shouldUseMock = (): boolean => {
  // Always use real API implementation
  return false;
};

/**
 * Generic API request function with standardized error handling
 */
export const apiRequest = async <T>(
  endpoint: string,
  method: string = 'GET',
  body?: any
): Promise<ApiResponse<T>> => {
  try {
    const url = endpoint.startsWith('http') ? endpoint : `${API_BASE_URL}${endpoint}`;
    
    console.log(`Making ${method} request to: ${url}`, body ? JSON.stringify(body).substring(0, 100) + '...' : 'no body');
    
    const response = await fetch(url, {
      method,
      headers: {
        'Content-Type': 'application/json',
      },
      body: body ? JSON.stringify(body) : undefined,
    });

    console.log(`Response status: ${response.status} ${response.statusText}`);
    console.log(`Response headers:`, Object.fromEntries([...response.headers.entries()]));
    
    let responseText: string;
    
    try {
      responseText = await response.text();
      console.log(`Response text (first 200 chars): ${responseText.substring(0, 200)}${responseText.length > 200 ? '...' : ''}`);
    } catch (textError) {
      console.error('Error getting response text:', textError);
      responseText = 'Could not read response body';
    }
    
    if (!response.ok) {
      console.error(`API request failed with status ${response.status}:`, responseText);
      
      let errorData: { message?: string; error?: string } = {};
      try {
        // Try to parse as JSON
        errorData = JSON.parse(responseText) as { message?: string; error?: string };
      } catch (parseError) {
        // Not JSON, use text as error message
        errorData = {
          message: `API request failed with status ${response.status}: ${responseText.substring(0, 100)}${responseText.length > 100 ? '...' : ''}`
        };
      }
      
      return {
        success: false,
        message: errorData.message || errorData.error || `API request failed with status ${response.status}`
      };
    }

    let responseData: Record<string, any>;
    try {
      // Try to parse as JSON
      responseData = JSON.parse(responseText) as Record<string, any>;
      console.log('Parsed response data (structure):', 
        JSON.stringify(
          // Create a simplified version to avoid console clutter
          Object.keys(responseData).reduce((acc: Record<string, any>, key: string) => {
            if (typeof responseData[key] === 'object' && responseData[key] !== null) {
              acc[key] = `[${typeof responseData[key]}]`;
            } else {
              acc[key] = responseData[key];
            }
            return acc;
          }, {})
        )
      );
    } catch (parseError) {
      console.error('Error parsing response as JSON:', parseError);
      return {
        success: false,
        message: `Failed to parse JSON response: ${responseText.substring(0, 100)}${responseText.length > 100 ? '...' : ''}`
      };
    }
    
    // Handle both new and old API response formats
    if (responseData.hasOwnProperty('success')) {
      // New format with success property directly in the response
      console.log('Response has success property:', responseData.success);
      
      // Make sure to preserve all properties from the response
      return {
        ...responseData,
        // Ensure these properties are always present
        success: responseData.success,
        data: responseData.data || null,
        message: responseData.message || responseData.error || null
      };
    } else {
      // Old format - wrap in new format
      console.log('Response using old format without success property');
      return {
        success: true,
        data: responseData as unknown as T
      };
    }
  } catch (error) {
    console.error('API request error:', error);
    return {
      success: false,
      message: error instanceof Error ? error.message : 'An unknown error occurred',
    };
  }
};

/**
 * Helper function to handle API errors consistently
 */
export const handleApiError = (error: any): void => {
  if (error && error.response && error.response.data) {
    console.error('API Error:', error.response.data.message || 'Unknown error');
  } else if (error && error.message) {
    console.error('API Error:', error.message);
  } else {
    console.error('Unknown API Error:', error);
  }
};

// Verification-specific API functions
export const generateSMTConstraints = async (
  program: string,
  mode: 'verify' | 'equivalence' = 'verify',
  secondProgram?: string
): Promise<ApiResponse<{ smtConstraints: string }>> => {
  // Use mock data during development
  if (shouldUseMock()) {
    try {
      const mockConstraints = await generateMockSMTConstraints(
        program,
        mode === 'equivalence',
        secondProgram
      );
      
      return {
        success: true,
        data: {
          smtConstraints: mockConstraints,
        },
      };
    } catch (error) {
      return {
        success: false,
        message: error instanceof Error ? error.message : 'An error occurred generating mock constraints',
      };
    }
  }

  // Real API call
  const endpoint = mode === 'verify' ? '/verify/generate-smt' : '/equivalence/generate-smt';
  return apiRequest<{ smtConstraints: string }>(
    endpoint,
    'POST',
    {
      program,
      ...(mode === 'equivalence' && { secondProgram }),
    }
  );
};

// Function to verify assertions in a program
export const verifyProgram = async (
  program: string,
  options?: Record<string, any>
): Promise<ApiResponse<{
  verified: boolean;
  counterexamples?: Array<{ [key: string]: any }>;
}>> => {
  if (shouldUseMock()) {
    // Simple mock verification result
    const hasFailing = program.includes('assert') && Math.random() > 0.5;
    
    return {
      success: true,
      data: {
        verified: !hasFailing,
        ...(hasFailing && {
          counterexamples: [
            { x: 0, y: -1 },
            { x: 5, y: -10 },
          ],
        }),
      },
    };
  }

  return apiRequest<{
    verified: boolean;
    counterexamples?: Array<{ [key: string]: any }>;
  }>('/verify', 'POST', { program, options });
};

// Function to check program equivalence
export const checkEquivalence = async (
  program1: string,
  program2: string,
  options?: Record<string, any>
): Promise<ApiResponse<{
  equivalent: boolean;
  counterexample?: { [key: string]: any };
}>> => {
  if (shouldUseMock()) {
    // Simple mock equivalence check
    const isEquivalent = program1.length === program2.length || Math.random() > 0.7;
    
    return {
      success: true,
      data: {
        equivalent: isEquivalent,
        ...(!isEquivalent && {
          counterexample: {
            input: { x: 3, y: 4 },
            output1: 11,
            output2: 7,
          },
        }),
      },
    };
  }

  return apiRequest<{
    equivalent: boolean;
    counterexample?: { [key: string]: any };
  }>('/equivalence', 'POST', { program1, program2, options });
};
