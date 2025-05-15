// Verification types definition

/**
 * Verification mode for the analyzer
 * - 'verification': Check if a single program satisfies its assertions
 * - 'equivalence': Check if two programs are semantically equivalent
 */
export type VerificationMode = 'verification' | 'equivalence';

/**
 * Status of a verification result
 */
export type ResultStatus = 'success' | 'failure' | 'error' | 'pending' | null;

/**
 * Type for view tabs in the UI
 */
export type ViewTab = 'results' | 'ssa' | 'optimized-ssa' | 'smt' | 'cfg';

/**
 * Type for visualizations
 */
export type VisualizationType = 'ast' | 'cfg' | 'none';

/**
 * Error types for better error handling
 */
export type ErrorType = 'parser' | 'transformer' | 'solver' | 'network' | 'generic';

/**
 * Error details structure
 */
export interface ErrorDetails {
  type: ErrorType;
  message: string;
  details?: string;
  line?: number;
  column?: number;
}

/**
 * Trace step for execution traces
 */
export interface TraceStep {
  line: number;
  statement: string;
  state?: Record<string, any>;
  branchTaken?: string;
  conditionResult?: boolean;
  assertionResult?: boolean;
  variableChanged?: string;
  arrayChanged?: string;
}

/**
 * Counterexample structure
 */
export interface Counterexample {
  inputs: Record<string, any>;
  outputs?: Record<string, any>;
  path?: string[];
  trace?: TraceStep[];
  variables?: Record<string, any>;
  failedAssertion?: string;
}

/**
 * CFG Node structure
 */
export interface CFGNode {
  id: string;
  label: string;
  data?: any;
}

/**
 * CFG Edge structure
 */
export interface CFGEdge {
  source: string;
  target: string;
  label?: string;
}

/**
 * Verification result from the API
 */
export interface VerificationResult {
  success: boolean;
  verified: boolean;
  message?: string;
  counterexamples?: Counterexample[];
  executionTime?: number;
  timedOut?: boolean;
  error?: string;
  mode?: VerificationMode;
}

/**
 * Equivalence check result from the API
 */
export interface EquivalenceResult {
  success: boolean;
  equivalent: boolean;
  message?: string;
  counterexample?: Counterexample;
  counterexamples?: Counterexample[];
  executionTime?: number;
  timedOut?: boolean;
  error?: string;
  mode?: VerificationMode;
} 