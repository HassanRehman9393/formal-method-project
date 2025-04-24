/**
 * Configuration module for loop handling
 */

// Default loop handling configuration
export const defaultLoopConfig = {
  // Whether to handle loops
  handleLoops: true,
  
  // Maximum loop unrolling depth
  unrollDepth: 5,
  
  // Whether to unroll all loops or just determinable ones
  unrollAll: false,
  
  // Instruction limit for loop body (prevents excessive unrolling)
  instructionLimit: 1000,
  
  // Strategy for handling loops
  // - "unroll": Unroll loops up to specified depth
  // - "symbolic": Use symbolic execution with loop invariants
  // - "hybrid": Combine unrolling with symbolic execution
  strategy: "unroll"
};

/**
 * Create loop handling configuration
 * @param {object} options - User-provided options
 * @returns {object} Complete configuration with defaults filled in
 */
export function createLoopConfig(options = {}) {
  return {
    ...defaultLoopConfig,
    ...options
  };
}
