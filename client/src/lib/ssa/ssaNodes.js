/**
 * SSA Nodes Module
 * 
 * Defines classes for representing SSA program elements
 */

/**
 * Represents a basic block in SSA form
 */
export class Block {
  constructor(label) {
    this.label = label || 'unnamed';
    this.phiFunctions = [];
    this.instructions = [];
    this.terminator = null;
  }

  /**
   * Add a phi function to the block
   * @param {PhiFunction} phiFunction - The phi function to add
   */
  insertPhiFunction(phiFunction) {
    if (!phiFunction) return;
    this.phiFunctions.push(phiFunction);
  }

  /**
   * Add an instruction to the block
   * @param {object} instruction - The instruction to add
   */
  addInstruction(instruction) {
    if (!instruction) return;
    this.instructions.push(instruction);
  }

  /**
   * Add a jump instruction (goto) as the block terminator
   * @param {string} target - Target block label
   */
  addJump(target) {
    if (!target) {
      console.warn('Attempted to add jump with no target');
      return;
    }
    this.terminator = {
      type: 'Jump',
      target
    };
  }

  /**
   * Add a conditional branch instruction as the block terminator
   * @param {object} condition - Branch condition
   * @param {string} thenTarget - Target block label when condition is true
   * @param {string} elseTarget - Target block label when condition is false
   */
  addBranch(condition, thenTarget, elseTarget) {
    if (!thenTarget || !elseTarget) {
      console.warn('Attempted to add branch with missing targets');
      return;
    }
    this.terminator = {
      type: 'Branch',
      condition,
      thenTarget,
      elseTarget
    };
  }

  /**
   * Add a return instruction as the block terminator
   * @param {*} value - Return value (optional)
   */
  addReturn(value = null) {
    this.terminator = {
      type: 'Return',
      value
    };
  }

  /**
   * Check if this block has a terminator instruction
   * @returns {boolean} True if the block has a terminator
   */
  hasTerminator() {
    return this.terminator !== null;
  }
}

/**
 * Represents a phi function in SSA form
 */
export class PhiFunction {
  /**
   * Create a new phi function
   * @param {string} variable - Original variable name
   * @param {string} target - SSA variable name (target of phi)
   * @param {string[]} sources - Source block labels
   */
  constructor(variable, target, sources = []) {
    this.variable = variable || 'unknown'; // Original variable name
    this.target = target || `${this.variable}_phi`;  // SSA variable name (e.g., "x_3")
    this.sources = Array.isArray(sources) ? sources : [];   // Source block labels
  }
}

/**
 * Represents a variable in SSA form
 */
export class Variable {
  /**
   * Create a new SSA variable
   * @param {string} name - Base variable name
   * @param {number} version - SSA version number
   */
  constructor(name, version) {
    this.name = name;       // Base name (e.g., "x")
    this.version = version; // SSA version (e.g., 3 for "x_3")
  }

  /**
   * Get the full SSA variable name
   * @returns {string} Full SSA variable name (e.g., "x_3")
   */
  toString() {
    return `${this.name}_${this.version}`;
  }
}

/**
 * Represents an assignment instruction in SSA form
 */
export class Assignment {
  /**
   * Create a new assignment instruction
   * @param {string} target - Target SSA variable name
   * @param {*} value - Value expression
   */
  constructor(target, value) {
    this.target = target; // Target SSA variable (e.g., "x_3")
    this.value = value;   // Value expression (can be complex object)
  }
}
