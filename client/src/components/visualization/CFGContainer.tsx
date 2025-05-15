import React, { useState, useEffect, Component, ErrorInfo, ReactNode } from 'react';
import CFGView from './CFGView';
import StaticCFGView from './StaticCFGView';
import SimpleCFGView from './SimpleCFGView';
import ReactFlowCFGView from './ReactFlowCFGView';
import PathHighlighter from './PathHighlighter';
import { generateCFG } from '../../lib/visualizer/cfgGenerator';
import { CFGNode, CFGEdge, ExecutionPath } from '../../types/visualization';
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { LoadingState } from "../ui/loading-state";
import { AlertCircle } from "lucide-react";

interface CFGContainerProps {
  ast: any; // The abstract syntax tree of the program
  ssaAst: any; // The SSA form of the program
  paths?: ExecutionPath[];
  title?: string;
}

// Error boundary component to catch errors in CFG visualization
class CFGErrorBoundary extends Component<{ 
  children: ReactNode, 
  fallback: ReactNode 
}, { 
  hasError: boolean 
}> {
  constructor(props: { children: ReactNode, fallback: ReactNode }) {
    super(props);
    this.state = { hasError: false };
  }

  static getDerivedStateFromError(_: Error) {
    return { hasError: true };
  }

  componentDidCatch(error: Error, errorInfo: ErrorInfo) {
    console.error("CFG visualization error:", error, errorInfo);
  }

  render() {
    if (this.state.hasError) {
      return this.props.fallback;
    }

    return this.props.children;
  }
}

const CFGContainer: React.FC<CFGContainerProps> = ({ 
  ast, 
  ssaAst, 
  paths = [],
  title = "Control Flow Graph"
}) => {
  const [originalCfg, setOriginalCfg] = useState<{ nodes: CFGNode[], edges: CFGEdge[] } | null>(null);
  const [ssaCfg, setSsaCfg] = useState<{ nodes: CFGNode[], edges: CFGEdge[] } | null>(null);
  const [highlightedPath, setHighlightedPath] = useState<string[]>([]);
  const [activeNodeId, setActiveNodeId] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState<boolean>(false);
  const [error, setError] = useState<Error | null>(null);
  
  // Generate CFGs from ASTs
  useEffect(() => {
    if (ast || ssaAst) {
      setIsLoading(true);
      setError(null);
      
      // Use setTimeout to avoid blocking the UI
      setTimeout(() => {
        try {
          if (ast) {
            const cfg = generateCFG(ast, false);
            setOriginalCfg(cfg);
          }
          
          if (ssaAst) {
            const cfg = generateCFG(ssaAst, true);
            setSsaCfg(cfg);
          }
        } catch (error) {
          console.error("Error generating CFG:", error);
          setError(error instanceof Error ? error : new Error("Unknown error generating CFG"));
        } finally {
          setIsLoading(false);
        }
      }, 100);
    }
  }, [ast, ssaAst]);
  
  // Handle path changes for highlighting
  const handlePathChange = (path: string[]) => {
    setHighlightedPath(path);
  };
  
  // Handle node highlighting
  const handleNodeHighlight = (nodeId: string | null) => {
    setActiveNodeId(nodeId);
  };
  
  if (isLoading) {
    return (
      <Card className="w-full">
        <CardHeader className="pb-2">
          <CardTitle>{title}</CardTitle>
        </CardHeader>
        <CardContent>
          <LoadingState message="Generating control flow graph..." />
        </CardContent>
      </Card>
    );
  }
  
  if (error) {
    return (
      <Card className="w-full">
        <CardHeader className="pb-2">
          <CardTitle>{title}</CardTitle>
        </CardHeader>
        <CardContent>
          <div className="flex flex-col items-center justify-center h-[400px] text-destructive">
            <AlertCircle className="h-12 w-12 mb-4" />
            <p className="font-semibold">Error generating Control Flow Graph</p>
            <p className="text-sm text-muted-foreground">{error.message}</p>
          </div>
        </CardContent>
      </Card>
    );
  }
  
  // Define static fallback view for when errors occur
  const staticFallbackView = (
    <StaticCFGView
      originalGraph={originalCfg}
      ssaGraph={ssaCfg}
      onNodeClick={handleNodeHighlight}
    />
  );
  
  return (
    <div className="space-y-4">
      <CFGErrorBoundary fallback={staticFallbackView}>
        <ReactFlowCFGView
          originalGraph={originalCfg}
          ssaGraph={ssaCfg}
          highlightedPath={highlightedPath}
          onNodeClick={handleNodeHighlight}
        />
      </CFGErrorBoundary>
      
      {paths.length > 0 && (
        <PathHighlighter
          paths={paths}
          onPathChange={handlePathChange}
          onHighlightNode={handleNodeHighlight}
          activeNodeId={activeNodeId}
        />
      )}
    </div>
  );
};

export default CFGContainer;
