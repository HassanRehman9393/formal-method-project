import React, { createContext, useContext, useState, ReactNode } from 'react';

// Step 1: Define more comprehensive types for our application state
export type VerificationMode = 'verification' | 'equivalence';
export type ResultStatus = 'success' | 'failure' | 'error' | 'pending' | null;
export type ViewTab = 'results' | 'ssa' | 'optimized-ssa' | 'smt' | 'cfg';
export type VisualizationType = 'ast' | 'cfg' | 'none';

// Define error types for better error handling
export type ErrorType = 'parser' | 'transformer' | 'solver' | 'network' | 'generic';

export interface ErrorDetails {
  type: ErrorType;
  message: string;
  details?: string;
  line?: number;
  column?: number;
}

export interface Counterexample {
  inputs: Record<string, any>;
  outputs?: Record<string, any>;
  path?: string[];
  trace?: Array<{
    line: number;
    state: Record<string, any>;
  }>;
}

// Define the context shape
interface VerificationContextType {
  // Mode
  mode: VerificationMode;
  setMode: (mode: VerificationMode) => void;
  
  // Code input
  program1: string;
  setProgram1: (code: string) => void;
  program2: string;
  setProgram2: (code: string) => void;
  
  // Configuration
  loopUnrollingDepth: number;
  setLoopUnrollingDepth: (depth: number) => void;
  
  // UI state
  activeTab: ViewTab;
  setActiveTab: (tab: ViewTab) => void;
  visualizationType: VisualizationType;
  setVisualizationType: (type: VisualizationType) => void;
  
  // Results
  ssaCode1: string;
  ssaCode2: string;
  optimizedSsaCode1: string;
  optimizedSsaCode2: string;
  smtConstraints: string;
  resultStatus: ResultStatus;
  resultMessage: string;
  counterexample: Counterexample | null;
  
  // Loading and error states
  isProcessing: boolean;
  isParsingCode: boolean;
  isTransformingSsa: boolean;
  isGeneratingSmtConstraints: boolean;
  isSolving: boolean;
  error: ErrorDetails | null;
  
  // Actions
  runVerification: () => void;
  resetResults: () => void;
  clearError: () => void;
  
  // Performance metrics (for UI feedback)
  executionTime: number | null;

  // Add these properties if they don't exist:
  ast1: any;
  ast2: any;
  ssaAst1: any;
  ssaAst2: any;
}

// Create the context with undefined initial value
const VerificationContext = createContext<VerificationContextType | undefined>(undefined);

// Custom hook for using the context
export const useVerification = () => {
  const context = useContext(VerificationContext);
  if (context === undefined) {
    throw new Error('useVerification must be used within a VerificationProvider');
  }
  return context;
};

interface VerificationProviderProps {
  children: ReactNode;
}

// Provider component
export const VerificationProvider: React.FC<VerificationProviderProps> = ({ children }) => {
  // Core state
  const [mode, setMode] = useState<VerificationMode>('verification');
  const [program1, setProgram1] = useState<string>('');
  const [program2, setProgram2] = useState<string>('');
  const [loopUnrollingDepth, setLoopUnrollingDepth] = useState<number>(5);
  
  // UI state
  const [activeTab, setActiveTab] = useState<ViewTab>('results');
  const [visualizationType, setVisualizationType] = useState<VisualizationType>('none');
  
  // Result states
  const [ssaCode1, setSsaCode1] = useState<string>('');
  const [ssaCode2, setSsaCode2] = useState<string>('');
  const [optimizedSsaCode1, setOptimizedSsaCode1] = useState<string>('');
  const [optimizedSsaCode2, setOptimizedSsaCode2] = useState<string>('');
  const [smtConstraints, setSmtConstraints] = useState<string>('');
  const [resultStatus, setResultStatus] = useState<ResultStatus>(null);
  const [resultMessage, setResultMessage] = useState<string>('');
  const [counterexample, setCounterexample] = useState<Counterexample | null>(null);
  const [executionTime, setExecutionTime] = useState<number | null>(null);
  
  // Loading states
  const [isProcessing, setIsProcessing] = useState<boolean>(false);
  const [isParsingCode, setIsParsingCode] = useState<boolean>(false);
  const [isTransformingSsa, setIsTransformingSsa] = useState<boolean>(false);
  const [isGeneratingSmtConstraints, setIsGeneratingSmtConstraints] = useState<boolean>(false);
  const [isSolving, setIsSolving] = useState<boolean>(false);
  
  // Error state
  const [error, setError] = useState<ErrorDetails | null>(null);
  
  // Clear error
  const clearError = () => setError(null);
  
  // Reset results
  const resetResults = () => {
    setSsaCode1('');
    setSsaCode2('');
    setOptimizedSsaCode1('');
    setOptimizedSsaCode2('');
    setSmtConstraints('');
    setResultStatus(null);
    setResultMessage('');
    setCounterexample(null);
    setExecutionTime(null);
    clearError();
  };
  
  // Run verification with step-by-step status updates
  const runVerification = async () => {
    if (!program1 || (mode === 'equivalence' && !program2)) {
      setError({
        type: 'generic',
        message: 'Please enter code in the editor before verifying.'
      });
      return;
    }
    
    // Reset previous results
    resetResults();
    
    // Start timing
    const startTime = Date.now();
    
    // Update processing states
    setIsProcessing(true);
    setResultStatus('pending');
    
    try {
      // Step 1: Parse Code
      setIsParsingCode(true);
      await new Promise(resolve => setTimeout(resolve, 500)); // Simulate API delay
      setIsParsingCode(false);
      
      // Step 2: Transform to SSA
      setIsTransformingSsa(true);
      await new Promise(resolve => setTimeout(resolve, 800)); // Simulate API delay
      
      // Update SSA code (mock data)
      setSsaCode1(`function main() {
  var x_0 = 0;
  var i_0 = 0;
  while (i_0 < 10) {
    var i_1 = i_0 + 1;
    var x_1 = x_0 + i_1;
    i_0 = i_1;
    x_0 = x_1;
  }
  assert(x_0 >= 0);
  return x_0;
}`);
      
      // Update optimized SSA code (mock data)
      setOptimizedSsaCode1(`function main() {
  var x_0 = 0; // Initialized variable
  var i_0 = 0; // Initialized variable
  while (i_0 < 10) { // Loop condition
    var i_1 = i_0 + 1; // Increment
    var x_1 = x_0 + i_1; // Updated sum
    i_0 = i_1; // Reassignment
    x_0 = x_1; // Reassignment
  }
  assert(x_0 >= 0); // Assertion
  return x_0; // Return statement
}`);
      
      if (mode === 'equivalence') {
        setSsaCode2(`function program2() {
  var sum_0 = 0;
  for (var i_0 = 1; i_0 <= 10; i_0 = i_0 + 1) {
    var sum_1 = sum_0 + i_0;
    sum_0 = sum_1;
  }
  var x_0 = sum_0;
  assert(x_0 >= 0);
  return x_0;
}`);
        
        setOptimizedSsaCode2(`function program2() {
  var sum_0 = 0; // Initialized variable
  for (var i_0 = 1; i_0 <= 10; i_0 = i_0 + 1) { // For loop
    var sum_1 = sum_0 + i_0; // Adding i to sum
    sum_0 = sum_1; // Reassignment
  }
  var x_0 = sum_0; // Assignment
  assert(x_0 >= 0); // Assertion
  return x_0; // Return statement
}`);
      }
      
      setIsTransformingSsa(false);
      
      // Step 3: Generate SMT Constraints
      setIsGeneratingSmtConstraints(true);
      await new Promise(resolve => setTimeout(resolve, 600)); // Simulate API delay
      
      // Set SMT constraints (mock data)
      if (mode === 'verification') {
        setSmtConstraints(`(declare-const x_0 Int)
(declare-const i_0 Int)
(declare-const i_1 Int)
(declare-const x_1 Int)

(assert (= x_0 0))
(assert (= i_0 0))
(assert (< i_0 10))
(assert (= i_1 (+ i_0 1)))
(assert (= x_1 (+ x_0 i_1)))
(assert (not (>= x_1 0)))

(check-sat)
(get-model)`);
      } else {
        setSmtConstraints(`(declare-const x1_0 Int)
(declare-const i1_0 Int)
(declare-const x2_0 Int)
(declare-const sum_0 Int)
(declare-const i2_0 Int)

; Program 1 constraints
(assert (= x1_0 0))
(assert (= i1_0 0))
; ... more constraints ...

; Program 2 constraints
(assert (= sum_0 0))
(assert (= i2_0 1))
; ... more constraints ...

; Check equivalence
(assert (not (= (program1) (program2))))

(check-sat)
(get-model)`);
      }
      
      setIsGeneratingSmtConstraints(false);
      
      // Step 4: Solve Constraints
      setIsSolving(true);
      await new Promise(resolve => setTimeout(resolve, 1000)); // Simulate API delay
      setIsSolving(false);
      
      // Randomly decide outcome for demo purposes
      const isSuccess = Math.random() > 0.5;
      
      if (isSuccess) {
        setResultStatus('success');
        if (mode === 'verification') {
          setResultMessage('All assertions have been verified. The program is correct for all possible inputs.');
        } else {
          setResultMessage('The programs are semantically equivalent. They produce the same output for all possible inputs.');
        }
        setCounterexample(null);
      } else {
        setResultStatus('failure');
        if (mode === 'verification') {
          setResultMessage('Assertion failed: x_0 >= 0 may not always be true.');
          setCounterexample({
            inputs: {
              i_0: 5,
              x_0: -10,
            },
            trace: [
              { line: 1, state: { x_0: 0, i_0: 0 } },
              { line: 4, state: { x_0: 0, i_0: 0, i_1: 1 } },
              { line: 5, state: { x_0: 0, i_0: 0, i_1: 1, x_1: 1 } },
              { line: 6, state: { x_0: 0, i_0: 1, i_1: 1, x_1: 1 } },
              { line: 7, state: { x_0: 1, i_0: 1, i_1: 1, x_1: 1 } },
            ]
          });
        } else {
          setResultMessage('The programs are not equivalent. There exists an input for which they produce different outputs.');
          setCounterexample({
            inputs: {
              i: 5,
            },
            outputs: {
              program1: 55,
              program2: 50,
            }
          });
        }
      }
      
      // Calculate execution time
      setExecutionTime(Date.now() - startTime);
      
    } catch (err) {
      console.error("Verification error:", err);
      setResultStatus('error');
      setError({
        type: 'generic',
        message: `An error occurred during verification: ${err instanceof Error ? err.message : String(err)}`
      });
    } finally {
      setIsProcessing(false);
      setIsParsingCode(false);
      setIsTransformingSsa(false);
      setIsGeneratingSmtConstraints(false);
      setIsSolving(false);
    }
  };
  
  // Combine all state and handlers into a single value object
  const value = {
    // Core state
    mode,
    setMode,
    program1,
    setProgram1,
    program2,
    setProgram2,
    loopUnrollingDepth,
    setLoopUnrollingDepth,
    
    // UI state
    activeTab,
    setActiveTab,
    visualizationType,
    setVisualizationType,
    
    // Results
    ssaCode1,
    ssaCode2,
    optimizedSsaCode1,
    optimizedSsaCode2,
    smtConstraints,
    resultStatus,
    resultMessage,
    counterexample,
    executionTime,
    
    // Loading states
    isProcessing,
    isParsingCode,
    isTransformingSsa,
    isGeneratingSmtConstraints,
    isSolving,
    error,
    
    // Actions
    runVerification,
    resetResults,
    clearError,

    // Add these properties if they don't exist:
    ast1: null,
    ast2: null,
    ssaAst1: null,
    ssaAst2: null,
  };
  
  return (
    <VerificationContext.Provider value={value}>
      {children}
    </VerificationContext.Provider>
  );
};
