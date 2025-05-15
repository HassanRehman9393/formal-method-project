import React, { useState, useCallback, useMemo } from 'react';
import { 
  Card, 
  CardContent, 
  CardHeader, 
  CardTitle 
} from "../ui/card";
import { Switch } from "../ui/switch";
import { Label } from "../ui/label";
import { CFGNode, CFGEdge } from "../../types/visualization";
import { Button } from '../ui/button';
import { ZoomIn, ZoomOut, RefreshCw } from 'lucide-react';
import ReactFlow, {
  ReactFlowProvider,
  Controls,
  Background,
  Node,
  Edge,
  useReactFlow,
  Panel,
  NodeTypes,
  EdgeTypes
} from 'reactflow';
import 'reactflow/dist/style.css';

interface SimpleCFGViewProps {
  originalGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  ssaGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  highlightedPath?: string[];
  onNodeClick?: (nodeId: string) => void;
}

// Custom node renderer for different node types
const CustomNode = ({ data, id }: { data: any, id: string }) => {
  const isHighlighted = data.isHighlighted;
  
  // Determine node style based on type and highlighting
  const getNodeStyle = () => {
    let backgroundColor = '#f5f5f5'; // default light gray
    
    switch (data.type) {
      case 'entry': backgroundColor = '#c8e6c9'; break; // light green
      case 'exit': backgroundColor = '#ffccbc'; break; // light red
      case 'condition': backgroundColor = '#bbdefb'; break; // light blue
      case 'join': backgroundColor = '#e1bee7'; break; // light purple
      case 'assert': backgroundColor = '#fff9c4'; break; // light yellow
      default: backgroundColor = '#f5f5f5'; break;
    }
    
    return {
      backgroundColor,
      borderColor: isHighlighted ? '#ff7000' : '#666',
      borderWidth: isHighlighted ? 2 : 1,
      padding: '10px',
      borderRadius: '8px',
      width: '150px',
      textAlign: 'center' as const,
      fontSize: '12px',
      boxShadow: isHighlighted ? '0 0 10px rgba(255, 112, 0, 0.5)' : 'none'
    };
  };
  
  return (
    <div style={getNodeStyle()}>
      <div style={{ fontWeight: 'bold', marginBottom: '4px' }}>
        {data.label}
      </div>
      {data.code && (
        <div style={{ fontSize: '10px', color: '#666', maxHeight: '40px', overflow: 'hidden' }}>
          {data.code.length > 30 ? data.code.substring(0, 27) + '...' : data.code}
        </div>
      )}
    </div>
  );
};

// Custom edge renderer
const CustomEdge = ({ id, sourceX, sourceY, targetX, targetY, data }: any) => {
  const isHighlighted = data?.isHighlighted || false;
  const edgePathId = `edge-path-${id}`;
  
  // Calculate the path
  const path = `M ${sourceX} ${sourceY} L ${targetX} ${targetY}`;
  
  return (
    <>
      <path
        id={edgePathId}
        d={path}
        stroke={isHighlighted ? '#ff7000' : '#999'}
        strokeWidth={isHighlighted ? 2 : 1}
        fill="none"
        markerEnd="url(#arrow)"
      />
      {data?.label && (
        <text>
          <textPath
            href={`#${edgePathId}`}
            startOffset="50%"
            textAnchor="middle"
            style={{
              fontSize: '10px',
              fill: isHighlighted ? '#ff7000' : '#666',
              dominantBaseline: 'central'
            }}
          >
            {data.label}
          </textPath>
        </text>
      )}
    </>
  );
};

// Define node types
const nodeTypes: NodeTypes = {
  customNode: CustomNode,
};

// Define edge types
const edgeTypes: EdgeTypes = {
  customEdge: CustomEdge,
};

// Flow chart component with React Flow
const FlowChart = ({ 
  graph, 
  highlightedPath = [], 
  onNodeClick 
}: { 
  graph: { nodes: CFGNode[], edges: CFGEdge[] }, 
  highlightedPath?: string[],
  onNodeClick?: (nodeId: string) => void 
}) => {
  const reactFlowInstance = useReactFlow();
  
  // Convert CFG data to React Flow format
  const flowNodes: Node[] = useMemo(() => {
    return graph.nodes.map((node) => {
      // Basic layout positioning using levels - can be improved
      const position = {
        x: (node.x !== undefined) ? node.x : Math.random() * 500,
        y: (node.y !== undefined) ? node.y : Math.random() * 500,
      };
      
      return {
        id: node.id,
        type: 'customNode',
        position,
        data: {
          ...node,
          isHighlighted: highlightedPath.includes(node.id),
        },
        // Make nodes draggable but maintain their positions
        draggable: true,
      };
    });
  }, [graph.nodes, highlightedPath]);
  
  const flowEdges: Edge[] = useMemo(() => {
    return graph.edges.map((edge, index) => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      
      // Check if this edge is on the highlighted path
      let isHighlighted = false;
      if (highlightedPath.length > 1) {
        for (let i = 0; i < highlightedPath.length - 1; i++) {
          if (highlightedPath[i] === sourceId && highlightedPath[i + 1] === targetId) {
            isHighlighted = true;
            break;
          }
        }
      }
      
      return {
        id: `edge-${index}-${sourceId}-${targetId}`,
        source: sourceId,
        target: targetId,
        type: 'customEdge',
        data: {
          label: edge.condition || edge.label || '',
          isHighlighted,
        },
        markerEnd: {
          type: 'arrow',
          width: 15,
          height: 15,
          color: isHighlighted ? '#ff7000' : '#999',
        },
        style: {
          stroke: isHighlighted ? '#ff7000' : '#999',
          strokeWidth: isHighlighted ? 2 : 1,
        },
      };
    });
  }, [graph.edges, highlightedPath]);
  
  // Handle node click
  const handleNodeClick = useCallback((_, node) => {
    if (onNodeClick) {
      onNodeClick(node.id);
    }
  }, [onNodeClick]);
  
  // Reset view to fit all nodes
  const resetView = useCallback(() => {
    if (reactFlowInstance && flowNodes.length > 0) {
      const padding = 0.2;
      reactFlowInstance.fitView({ padding });
    }
  }, [reactFlowInstance, flowNodes]);
  
  // Auto-layout the graph using a Dagre-like approach
  const layoutGraph = useCallback(() => {
    if (!reactFlowInstance || flowNodes.length === 0) return;
    
    // Simple hierarchical layout
    const nodeMap = new Map();
    flowNodes.forEach(node => nodeMap.set(node.id, node));
    
    // Find entry nodes (nodes without incoming edges)
    const incomingEdges = new Map();
    flowEdges.forEach(edge => {
      if (!incomingEdges.has(edge.target)) {
        incomingEdges.set(edge.target, []);
      }
      incomingEdges.get(edge.target).push(edge.source);
    });
    
    // Start with entry nodes (nodes with no incoming edges)
    const entryNodes = flowNodes
      .filter(node => !incomingEdges.has(node.id) || incomingEdges.get(node.id).length === 0)
      .map(node => node.id);
    
    // BFS to assign y-levels
    const visited = new Set();
    const levels = new Map();
    const queue = entryNodes.map(id => ({ id, level: 0 }));
    
    while (queue.length > 0) {
      const { id, level } = queue.shift()!;
      
      if (visited.has(id)) continue;
      visited.add(id);
      
      // Set the level
      levels.set(id, level);
      
      // Find outgoing edges
      const outgoingEdges = flowEdges.filter(edge => edge.source === id);
      
      // Add targets to queue
      outgoingEdges.forEach(edge => {
        if (!visited.has(edge.target)) {
          queue.push({ id: edge.target, level: level + 1 });
        }
      });
    }
    
    // Count nodes per level
    const nodesPerLevel = new Map();
    for (const [id, level] of levels.entries()) {
      if (!nodesPerLevel.has(level)) {
        nodesPerLevel.set(level, []);
      }
      nodesPerLevel.get(level).push(id);
    }
    
    // Assign x positions based on level
    const nodeWidth = 180;
    const nodeHeight = 80;
    const newNodes = flowNodes.map(node => {
      const level = levels.get(node.id) || 0;
      const nodesInLevel = nodesPerLevel.get(level) || [];
      const indexInLevel = nodesInLevel.indexOf(node.id);
      const levelWidth = nodesInLevel.length * nodeWidth;
      
      return {
        ...node,
        position: {
          x: (indexInLevel * nodeWidth) - (levelWidth / 2) + (nodeWidth / 2),
          y: level * nodeHeight,
        },
      };
    });
    
    // Update nodes with new positions
    reactFlowInstance.setNodes(newNodes);
    
    // Fit view to show all nodes
    setTimeout(() => {
      resetView();
    }, 50);
  }, [reactFlowInstance, flowNodes, flowEdges, resetView]);
  
  // Apply layout when nodes or edges change
  React.useEffect(() => {
    if (flowNodes.length > 0) {
      layoutGraph();
    }
  }, [flowNodes.length, layoutGraph]);
  
  return (
    <ReactFlow
      nodes={flowNodes}
      edges={flowEdges}
      onNodeClick={handleNodeClick}
      nodeTypes={nodeTypes}
      edgeTypes={edgeTypes}
      fitView
      attributionPosition="bottom-left"
    >
      <Panel position="top-right">
        <Button size="sm" variant="outline" onClick={resetView}>
          <RefreshCw className="h-4 w-4 mr-1" />
          Reset View
        </Button>
      </Panel>
      <Controls />
      <Background color="#aaa" gap={16} />
      <svg>
        <defs>
          <marker
            id="arrow"
            viewBox="0 0 10 10"
            refX="8"
            refY="5"
            markerWidth="8"
            markerHeight="8"
            orient="auto-start-reverse"
          >
            <path d="M 0 0 L 10 5 L 0 10 z" fill="#999" />
          </marker>
        </defs>
      </svg>
    </ReactFlow>
  );
};

// Main SimpleCFGView component
const SimpleCFGView: React.FC<SimpleCFGViewProps> = ({
  originalGraph,
  ssaGraph,
  highlightedPath = [],
  onNodeClick
}) => {
  const [showSsa, setShowSsa] = useState(false);
  
  // Create a default empty graph to avoid null issues
  const defaultGraph = { 
    nodes: [{ id: 'empty', label: 'No data', type: 'entry', code: 'No code available' }],
    edges: []
  };
  
  // Use default if graph is null or invalid
  const activeGraph = showSsa 
    ? (ssaGraph && ssaGraph.nodes && ssaGraph.nodes.length > 0 ? ssaGraph : defaultGraph) 
    : (originalGraph && originalGraph.nodes && originalGraph.nodes.length > 0 ? originalGraph : defaultGraph);

  return (
    <Card className="w-full">
      <CardHeader className="pb-2">
        <div className="flex items-center justify-between">
          <CardTitle>Control Flow Graph</CardTitle>
          <div className="flex items-center space-x-2">
            <Label htmlFor="show-ssa">Show SSA Form</Label>
            <Switch 
              id="show-ssa" 
              checked={showSsa} 
              onCheckedChange={setShowSsa}
              disabled={!ssaGraph}
            />
          </div>
        </div>
      </CardHeader>
      <CardContent>
        <div className="h-[600px] border rounded-md bg-background">
          <ReactFlowProvider>
            <FlowChart 
              graph={activeGraph} 
              highlightedPath={highlightedPath}
              onNodeClick={onNodeClick}
            />
          </ReactFlowProvider>
        </div>
      </CardContent>
    </Card>
  );
};

export default SimpleCFGView;