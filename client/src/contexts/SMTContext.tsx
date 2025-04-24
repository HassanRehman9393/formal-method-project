import React, { createContext, useContext, useState, ReactNode } from 'react';

interface SMTContextType {
  smtConstraints: string;
  isGenerating: boolean;
  error: string | null;
  generateConstraints: (programCode: string, mode: 'verify' | 'equivalence', secondProgram?: string) => Promise<void>;
}

const defaultContext: SMTContextType = {
  smtConstraints: '',
  isGenerating: false,
  error: null,
  generateConstraints: async () => {},
};

const SMTContext = createContext<SMTContextType>(defaultContext);

export const useSMT = () => useContext(SMTContext);

interface SMTProviderProps {
  children: ReactNode;
  apiUrl?: string;
}

export const SMTProvider: React.FC<SMTProviderProps> = ({ 
  children, 
  apiUrl = 'http://localhost:3001/api'
}) => {
  const [smtConstraints, setSmtConstraints] = useState<string>('');
  const [isGenerating, setIsGenerating] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  const generateConstraints = async (
    programCode: string, 
    mode: 'verify' | 'equivalence', 
    secondProgram?: string
  ) => {
    if (!programCode.trim()) {
      setError('No program code provided');
      return;
    }

    setIsGenerating(true);
    setError(null);

    try {
      const endpoint = mode === 'verify' ? `${apiUrl}/verify/generate-smt` : `${apiUrl}/equivalence/generate-smt`;
      
      const response = await fetch(endpoint, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          program: programCode,
          secondProgram: mode === 'equivalence' ? secondProgram : undefined,
        }),
      });

      if (!response.ok) {
        const errorData = await response.json();
        throw new Error(errorData.message || 'Failed to generate SMT constraints');
      }

      const data = await response.json();
      setSmtConstraints(data.smtConstraints);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'An unknown error occurred');
      console.error('SMT generation error:', err);
    } finally {
      setIsGenerating(false);
    }
  };

  return (
    <SMTContext.Provider
      value={{
        smtConstraints,
        isGenerating,
        error,
        generateConstraints,
      }}
    >
      {children}
    </SMTContext.Provider>
  );
};
