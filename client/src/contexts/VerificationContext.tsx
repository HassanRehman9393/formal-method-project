import React, { createContext, useContext, useState, ReactNode } from 'react';
import { 
  parseProgram, 
  transformToSSA, 
  generateSMTConstraints, 
  verifyProgram, 
  checkEquivalence 
} from '../lib/apiService';
import {
  VerificationMode,
  ResultStatus,
  ViewTab,
  VisualizationType,
  ErrorType,
  ErrorDetails,
  Counterexample,
  CFGNode,
  CFGEdge,
  TraceStep
} from '../types/verification';

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
  
  // CFG data
  cfgData: {
    program1: { 
      nodes: CFGNode[]; 
      edges: CFGEdge[]; 
      entryNode: string; 
      exitNode: string;
    } | null;
    program2: { 
      nodes: CFGNode[]; 
      edges: CFGEdge[]; 
      entryNode: string; 
      exitNode: string;
    } | null;
  };
  
  // Loading and error states
  isProcessing: boolean;
  isParsingCode: boolean;
  isTransformingSsa: boolean;
  isGeneratingSSA: boolean;
  isGeneratingSmtConstraints: boolean;
  isSolving: boolean;
  error: ErrorDetails | null;
  
  // Actions
  runVerification: () => void;
  resetResults: () => void;
  clearError: () => void;
  
  // Performance metrics (for UI feedback)
  executionTime: number | null;

  // AST and SSA AST
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
  
  // Add state to store AST and SSA AST
  const [astState, setAstState] = useState<{ast1: any; ast2: any}>({ast1: null, ast2: null});
  const [ssaState, setSSAState] = useState<{ssaAst1: any; ssaAst2: any}>({ssaAst1: null, ssaAst2: null});
  
  // Add control flow graph state
  const [cfgData, setCFGData] = useState<{
    program1: { 
      nodes: CFGNode[]; 
      edges: CFGEdge[]; 
      entryNode: string; 
      exitNode: string;
    } | null;
    program2: { 
      nodes: CFGNode[]; 
      edges: CFGEdge[]; 
      entryNode: string; 
      exitNode: string;
    } | null;
  }>({
    program1: null,
    program2: null
  });
  
  // Loading states
  const [isProcessing, setIsProcessing] = useState<boolean>(false);
  const [isParsingCode, setIsParsingCode] = useState<boolean>(false);
  const [isTransformingSsa, setIsTransformingSsa] = useState<boolean>(false);
  const [isGeneratingSSA, setIsGeneratingSSA] = useState<boolean>(false);
  const [isGeneratingSmtConstraints, setIsGeneratingSmtConstraints] = useState<boolean>(false);
  const [isSolving, setIsSolving] = useState<boolean>(false);
  
  // Error state
  const [error, setError] = useState<ErrorDetails | null>(null);
  
  // Clear error
  const clearError = () => setError(null);
  
  // Reset all results
  const resetResults = () => {
    console.log('Resetting all results and state');
    setSSAState({
      ssaCode1: '',
      optimizedSsaCode1: '',
      ssaCode2: '',
      optimizedSsaCode2: '',
      ssaAst1: null,
      ssaAst2: null
    });
    setAstState({
      ast1: null,
      ast2: null
    });
    setCFGData(null);
    setSmtConstraints('');
    setResultStatus(null);
    setResultMessage('');
    setCounterexample(null);
    setExecutionTime(null);
    clearError();
    setIsGeneratingSSA(false);
    setIsGeneratingSmtConstraints(false);
    setIsSolving(false);
  };
  
  // Process SSA transformation
  const proceedWithSSATransformation = async (
    prog1: string, 
    prog2: string | null, 
    mode: 'verification' | 'equivalence',
    ast1: any, 
    ast2: any
  ) => {
    try {
      // Store start time for performance tracking
      const startTime = Date.now();
      
      setIsTransformingSsa(true);
      
      // Step 2: Transform to SSA form
      console.log('Transforming to SSA...');
      
      // Store the original ASTs
      setAstState(prev => ({
        ...prev,
        ast1,
        ast2
      }));
      
      // Transform to SSA using real API service
      let ssa1Result;
      let ssa2Result;
      
      try {
        if (ast1) {
          ssa1Result = await transformToSSA(ast1, { loopUnrollingDepth });
        } else {
          // If AST is not available, parse the program first
          const parseResult = await parseProgram(prog1);
          if (parseResult?.success && parseResult?.ast) {
            ast1 = parseResult.ast;
            ssa1Result = await transformToSSA(ast1, { loopUnrollingDepth });
          } else {
            throw new Error('Failed to parse program 1');
          }
        }
        
        if (ssa1Result?.success) {
          console.log('SSA 1 transformed successfully');
          setSsaCode1(ssa1Result.ssaCode || '');
          setOptimizedSsaCode1(ssa1Result.optimizedSsaCode || '');
          setSSAState(prev => ({ ...prev, ssaAst1: ssa1Result.ssaAst }));
          
          // Generate CFG for program 1
          // Import the CFG generator here
          const { generateCFG } = await import('../lib/visualizer/cfgGenerator');
          
          try {
            const cfg1 = generateCFG(ast1, false);
            const ssaCfg1 = generateCFG(ssa1Result.ssaAst, true);
            
            // Update CFG data
            setCFGData(prev => ({
              ...prev,
              program1: {
                nodes: cfg1.nodes,
                edges: cfg1.edges,
                entryNode: 'entry',
                exitNode: 'exit'
              }
            }));
          } catch (cfgError) {
            console.error('Error generating CFG for program 1:', cfgError);
          }
        }
        
        // If in equivalence mode, also transform program 2
        if (mode === 'equivalence' && prog2) {
          console.log('Transforming program 2 to SSA...');
          
          if (ast2) {
            ssa2Result = await transformToSSA(ast2, { loopUnrollingDepth });
      } else {
            // If AST is not available, parse the program first
            const parseResult = await parseProgram(prog2);
            if (parseResult?.success && parseResult?.ast) {
              ast2 = parseResult.ast;
              ssa2Result = await transformToSSA(ast2, { loopUnrollingDepth });
      } else {
              throw new Error('Failed to parse program 2');
            }
          }
          
          if (ssa2Result?.success) {
            console.log('SSA 2 transformed successfully');
            setSsaCode2(ssa2Result.ssaCode || '');
            setOptimizedSsaCode2(ssa2Result.optimizedSsaCode || '');
            setSSAState(prev => ({ ...prev, ssaAst2: ssa2Result.ssaAst }));
            
            // Generate CFG for program 2
            const { generateCFG } = await import('../lib/visualizer/cfgGenerator');
            
            try {
              const cfg2 = generateCFG(ast2, false);
              const ssaCfg2 = generateCFG(ssa2Result.ssaAst, true);
              
              // Update CFG data
              setCFGData(prev => ({
                ...prev,
                program2: {
                  nodes: cfg2.nodes,
                  edges: cfg2.edges,
                  entryNode: 'entry',
                  exitNode: 'exit'
                }
              }));
            } catch (cfgError) {
              console.error('Error generating CFG for program 2:', cfgError);
            }
          }
        }
      } catch (error) {
        console.error('Error in SSA transformation:', error);
        setError({
          type: 'transformer',
          message: `Error transforming to SSA: ${error instanceof Error ? error.message : String(error)}`
        });
        setIsProcessing(false);
        return false;
      }
      
      setIsTransformingSsa(false);
      setIsGeneratingSSA(true);
      
      // Step 3: Generate SMT Constraints
      setIsGeneratingSmtConstraints(true);
      
      // Use the API service to generate SMT constraints
      let smtResult;
      
      try {
        console.log('Generating SMT constraints...');
        
        if (mode === 'equivalence' && prog2) {
          console.log('Equivalence check: Generating SMT constraints for both programs');
          // Use real API to generate constraints
          smtResult = await generateSMTConstraints(prog1, 'equivalence', prog2);
        } else {
          console.log('Verification: Generating SMT constraints for single program');
          // Use real API to generate constraints
          smtResult = await generateSMTConstraints(prog1);
        }
        
        console.log('SMT generation result:', {
          success: smtResult?.success,
          constraintsType: typeof smtResult?.smtConstraints,
          constraintsLength: smtResult?.smtConstraints?.length || 0,
          error: smtResult?.error || null
        });
        
        if (smtResult?.success && smtResult?.smtConstraints) {
          setSmtConstraints(smtResult.smtConstraints);
          } else {
          console.warn('No SMT constraints returned or error occurred');
          setError({
            type: 'generic',
            message: smtResult?.error || 'Failed to generate SMT constraints'
          });
          setIsProcessing(false);
          return false;
        }
      } catch (error) {
        console.error('Error generating SMT constraints:', error);
        setError({
          type: 'generic',
          message: `Error generating SMT constraints: ${error instanceof Error ? error.message : String(error)}`
        });
        setIsProcessing(false);
        return false;
      }
      
      setIsGeneratingSmtConstraints(false);
      
      // Step 4: Run solver for verification or equivalence checking
      setIsSolving(true);
      console.log(`Running ${mode} verification...`);

      try {
        let verificationResult;
        
        if (mode === 'verification') {
          // Run verification with the real verification service
          verificationResult = await verifyProgram(prog1, {
            loopUnrollingDepth
          });
        } else { // Equivalence mode
          if (!prog2) {
            throw new Error('Second program required for equivalence checking');
          }
          
          // Run equivalence check with the real equivalence service
          verificationResult = await checkEquivalence(prog1, prog2, {
            loopUnrollingDepth
          });
        }
        
        console.log(`${mode} result:`, verificationResult);
        
        if (!verificationResult?.success) {
          throw new Error(verificationResult?.error || `${mode} check failed`);
        }
        
        // Process verification result based on mode
        if (mode === 'verification') {
          console.log('Processing verification result:', verificationResult);
          
          if (!verificationResult) {
            console.error('No verification result returned');
            setError({
              type: 'generic',
              message: 'Verification failed - no result returned from verification API'
            });
            return false;
          }
          
          const { verified, counterexamples } = verificationResult;
          
          // Debug counterexamples
          console.log('Counterexamples received:', counterexamples);
          
          // Create a default counterexample if none are returned but verification failed
          let finalCounterexample = null;
          if (counterexamples && counterexamples.length > 0) {
            finalCounterexample = counterexamples[0];
            console.log('Using provided counterexample:', finalCounterexample);
          }
          
          // Set result based on verification status
          setResultStatus(verified ? 'success' : 'error');
          setResultMessage(verified ? 'All assertions verified!' : 'Assertion(s) failed. Check counterexamples.');
          setCounterexample(finalCounterexample);
          
          console.log(`Verification completed with result: ${verified ? 'VERIFIED' : 'FAILED'}`);
          console.log('Final counterexample set:', finalCounterexample);
        } else if (mode === 'equivalence') {
          console.log('Processing equivalence result:', verificationResult);
          
          if (!verificationResult) {
            console.error('No equivalence result returned');
            setError({
              type: 'generic',
              message: 'Equivalence check failed - no result returned from API'
            });
            return false;
          }
          
          const { equivalent, counterexamples } = verificationResult;
          
          // Debug counterexamples 
          console.log('Counterexamples received:', counterexamples);
          
          // Create a default counterexample if none are returned but equivalence failed
          let finalCounterexample = null;
          if (counterexamples && counterexamples.length > 0) {
            finalCounterexample = counterexamples[0];
            console.log('Using provided counterexample:', finalCounterexample);
          }
          
          // Set result based on equivalence status
          setResultStatus(equivalent ? 'success' : 'error');
          setResultMessage(equivalent ? 'Programs are semantically equivalent!' : 'Programs are not equivalent. Check counterexamples.');
          setCounterexample(finalCounterexample);
          
          console.log(`Equivalence check completed with result: ${equivalent ? 'EQUIVALENT' : 'NOT EQUIVALENT'}`);
          console.log('Final counterexample set:', finalCounterexample);
        }
        
        return true;
      } catch (error) {
        console.error(`Error in ${mode} verification:`, error);
        setError({
          type: 'solver',
          message: `Error in verification process: ${error instanceof Error ? error.message : String(error)}`
        });
        setResultStatus('error');
        setResultMessage(`Error: ${error instanceof Error ? error.message : String(error)}`);
        return false;
      } finally {
        setIsSolving(false);
        setIsProcessing(false);
      
      // Calculate execution time
        const endTime = Date.now();
        setExecutionTime(endTime - startTime);
      }
    } catch (error) {
      console.error('Unexpected error in verification workflow:', error);
      setError({
        type: 'generic',
        message: `Unexpected error: ${error instanceof Error ? error.message : String(error)}`
      });
      setIsProcessing(false);
      setIsSolving(false);
      setIsGeneratingSmtConstraints(false);
      setIsTransformingSsa(false);
      setIsParsingCode(false);
      return false;
    }
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
      
      // Use the API service to parse the code
      let ast1Result;
      let ast2Result;
      
      try {
        console.log('Making parse request for program1:', program1?.substring(0, 50) + '...');
        ast1Result = await parseProgram(program1);
        console.log('Parse program 1 result success:', ast1Result?.success);
        console.log('Parse program 1 ast available:', !!ast1Result?.ast);
        
        if (ast1Result?.ast) {
          console.log('AST1 type:', typeof ast1Result.ast);
          console.log('AST1 structure (abbreviated):', 
            Object.keys(typeof ast1Result.ast === 'object' ? ast1Result.ast : {})
          );
        } else {
          console.warn('No AST returned for program 1');
        }
        
        // Special handling for broken API response format
        if (!ast1Result?.success && !ast1Result?.ast) {
          console.warn('Parse returned unsuccessful but API might have returned data. Checking parse result...');
          console.log('Full parse result:', JSON.stringify(ast1Result).substring(0, 200) + '...');
          // Try to use the original program for SSA transformation if parsing failed
          // This is a workaround for API inconsistency
          setIsParsingCode(false);
          return await proceedWithSSATransformation(program1, program2, mode, ast1Result.ast, mode === 'equivalence' ? ast2Result?.ast : null);
        }
        
        if (mode === 'equivalence') {
          console.log('Making parse request for program2:', program2?.substring(0, 50) + '...');
          ast2Result = await parseProgram(program2);
          console.log('Parse program 2 result success:', ast2Result?.success);
          console.log('Parse program 2 ast available:', !!ast2Result?.ast);
          
          if (ast2Result?.ast) {
            console.log('AST2 type:', typeof ast2Result.ast);
            console.log('AST2 structure (abbreviated):', 
              Object.keys(typeof ast2Result.ast === 'object' ? ast2Result.ast : {})
            );
          } else {
            console.warn('No AST returned for program 2');
          }
        }
      } catch (err) {
        console.error('Error during parsing:', err);
        console.log('Attempting to continue with original program code');
        // Try to proceed with SSA transformation using the original code
        setIsParsingCode(false);
        return await proceedWithSSATransformation(program1, program2, mode, ast1Result.ast, mode === 'equivalence' ? ast2Result?.ast : null);
      }
      
      // Check if parsing was successful but no AST was returned (API inconsistency)
      if (!ast1Result?.ast) {
        console.warn('Program 1 parsing succeeded but no AST was returned');
        console.log('Full ast1Result:', JSON.stringify(ast1Result).substring(0, 200) + '...');
        // Try to use the original program for SSA transformation
        setIsParsingCode(false);
        return await proceedWithSSATransformation(program1, program2, mode, ast1Result.ast, mode === 'equivalence' ? ast2Result?.ast : null);
      }
      
      if (mode === 'equivalence' && ast2Result && !ast2Result?.ast) {
        console.warn('Program 2 parsing succeeded but no AST was returned');
        console.log('Full ast2Result:', JSON.stringify(ast2Result).substring(0, 200) + '...');
      }
      
      setIsParsingCode(false);
      
      return await proceedWithSSATransformation(
        program1, 
        program2, 
        mode,
        ast1Result.ast, 
        mode === 'equivalence' ? ast2Result?.ast : null
      );
    } catch (err) {
      console.error('Error in verification process:', err);
      setResultStatus('error');
      setError({
        type: 'generic',
        message: `An error occurred during verification: ${err instanceof Error ? err.message : String(err)}`
      });
      
      setIsProcessing(false);
      setIsParsingCode(false);
      setIsTransformingSsa(false);
      setIsGeneratingSmtConstraints(false);
      setIsSolving(false);
      return;
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
    
    // CFG data
    cfgData,
    
    // Loading states
    isProcessing,
    isParsingCode,
    isTransformingSsa,
    isGeneratingSSA,
    isGeneratingSmtConstraints,
    isSolving,
    error,
    
    // Actions
    runVerification,
    resetResults,
    clearError,

    // AST and SSA AST
    ast1: astState.ast1,
    ast2: astState.ast2,
    ssaAst1: ssaState.ssaAst1,
    ssaAst2: ssaState.ssaAst2,
  };
  
  return (
    <VerificationContext.Provider value={value}>
      {children}
    </VerificationContext.Provider>
  );
};
