/**
 * Type definitions for visualization components
 */

// Control Flow Graph Node type
export interface CFGNode {
  id: string;
  label: string;
  type: 'entry' | 'exit' | 'statement' | 'condition' | 'join' | 'assert';
  code: string;
  line?: number;
  inPaths?: string[];
  outPaths?: string[];
  isHighlighted?: boolean;
  // Properties required by D3.js force simulation
  x?: number;
  y?: number;
  fx?: number | null;
  fy?: number | null;
  vx?: number;
  vy?: number;
  index?: number;
}

// Control Flow Graph Edge type
export interface CFGEdge {
  source: string | CFGNode;
  target: string | CFGNode;
  label?: string;
  condition?: string;
  isHighlighted?: boolean;
}

// Execution Path for path highlighting
export interface ExecutionPath {
  id: string;
  name: string;
  description: string;
  nodes: string[];
}
