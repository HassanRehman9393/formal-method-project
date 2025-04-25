import React, { useState, useEffect } from 'react';
import CFGView from './CFGView';
import PathHighlighter from './PathHighlighter';
import { generateCFG } from '../../lib/visualizer/cfgGenerator';
import { CFGNode, CFGEdge, ExecutionPath } from '../../types/visualization';
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { LoadingState } from "../ui/loading-state";

interface CFGContainerProps {
  ast: any; // The abstract syntax tree of the program
  ssaAst: any; // The SSA form of the program
  paths?: ExecutionPath[];
  title?: string;
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
  
  // Generate CFGs from ASTs
  useEffect(() => {
    if (ast || ssaAst) {
      setIsLoading(true);
      
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
  
  return (
    <div className="space-y-4">
      <CFGView
        originalGraph={originalCfg}
        ssaGraph={ssaCfg}
        highlightedPath={highlightedPath}
        onNodeClick={handleNodeHighlight}
      />
      
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
