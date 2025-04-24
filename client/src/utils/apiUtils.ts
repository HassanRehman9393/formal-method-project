// API utility functions for interacting with the backend

import { generateMockSMTConstraints } from '../lib/mockSmtService';

interface ApiResponse<T> {
  data?: T;
  error?: string;
}

// Base API URL - can be configured from environment
const API_BASE_URL = import.meta.env.VITE_API_BASE_URL || 'http://localhost:3001/api';

// Function to determine if we should use mock data
// During development we can use mock data if the API is not yet available
const shouldUseMock = (): boolean => {
  return import.meta.env.VITE_USE_MOCK_API === 'true' || !API_BASE_URL;
};

// Generic API request function
export const apiRequest = async <T>(
  endpoint: string,
  method: string = 'GET',
  body?: any
): Promise<ApiResponse<T>> => {
  try {
    const response = await fetch(`${API_BASE_URL}${endpoint}`, {
      method,
      headers: {
        'Content-Type': 'application/json',
      },
      body: body ? JSON.stringify(body) : undefined,
    });

    if (!response.ok) {
      const errorData = await response.json();
      throw new Error(errorData.message || `API request failed with status ${response.status}`);
    }

    const data = await response.json();
    return { data };
  } catch (error) {
    return {
      error: error instanceof Error ? error.message : 'An unknown error occurred',
    };
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
        data: {
          smtConstraints: mockConstraints,
        },
      };
    } catch (error) {
      return {
        error: error instanceof Error ? error.message : 'An error occurred generating mock constraints',
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
  program: string
): Promise<ApiResponse<{
  valid: boolean;
  counterexamples?: Array<{ [key: string]: any }>;
}>> => {
  if (shouldUseMock()) {
    // Simple mock verification result
    const hasFailing = program.includes('assert') && Math.random() > 0.5;
    
    return {
      data: {
        valid: !hasFailing,
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
    valid: boolean;
    counterexamples?: Array<{ [key: string]: any }>;
  }>('/verify', 'POST', { program });
};

// Function to check program equivalence
export const checkEquivalence = async (
  program1: string,
  program2: string
): Promise<ApiResponse<{
  equivalent: boolean;
  counterexample?: { [key: string]: any };
}>> => {
  if (shouldUseMock()) {
    // Simple mock equivalence check
    const isEquivalent = program1.length === program2.length || Math.random() > 0.7;
    
    return {
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
  }>('/equivalence', 'POST', { program1, program2 });
};
