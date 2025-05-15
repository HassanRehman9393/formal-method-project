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
  EdgeTypes,
  Handle,
  Position,
  ConnectionLineType,
  NodeMouseHandler
} from 'reactflow';
import 'reactflow/dist/style.css';

interface ReactFlowCFGViewProps {
  originalGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  ssaGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  highlightedPath?: string[];
  onNodeClick?: (nodeId: string) => void;
}

// Create a type for the graph structure we use internally
interface CFGGraph {
  nodes: CFGNode[];
  edges: CFGEdge[];
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
      {/* Source handle - where connections start from */}
      <Handle
        type="source"
        position={Position.Bottom}
        id={`${id}-source`}
        style={{ background: '#555' }}
      />
      
      <div style={{ fontWeight: 'bold', marginBottom: '4px' }}>
        {data.label}
      </div>
      {data.code && (
        <div style={{ fontSize: '10px', color: '#666', maxHeight: '40px', overflow: 'hidden' }}>
          {data.code.length > 30 ? data.code.substring(0, 27) + '...' : data.code}
        </div>
      )}
      
      {/* Target handle - where connections end at */}
      <Handle
        type="target"
        position={Position.Top}
        id={`${id}-target`}
        style={{ background: '#555' }}
      />
    </div>
  );
};

// Define node types - moved outside component to prevent recreating on each render
const nodeTypes: NodeTypes = {
  customNode: CustomNode,
};

// Custom edge component
const CustomEdge = ({ 
  id, 
  sourceX, 
  sourceY, 
  targetX, 
  targetY, 
  sourcePosition,
  targetPosition,
  data,
  style = {}
}: any) => {
  const isHighlighted = data?.isHighlighted || false;
  const edgeColor = isHighlighted ? '#ff7000' : '#999';
  const strokeWidth = isHighlighted ? 2 : 1;
  
  // Calculate path
  const edgePath = getSmoothStepPath({
    sourceX,
    sourceY,
    sourcePosition,
    targetX,
    targetY,
    targetPosition,
  });
  
  return (
    <>
      <path
        id={id}
        className="react-flow__edge-path"
        d={edgePath}
        stroke={edgeColor}
        strokeWidth={strokeWidth}
        fill="none"
        markerEnd="url(#react-flow__arrowhead)"
      />
      {data?.label && (
        <text>
          <textPath
            href={`#${id}`}
            startOffset="50%"
            textAnchor="middle"
            dominantBaseline="central"
            style={{
              fontSize: '10px',
              fill: edgeColor,
              fontWeight: isHighlighted ? 'bold' : 'normal',
            }}
          >
            {data.label}
          </textPath>
        </text>
      )}
    </>
  );
};

// Helper function to calculate smooth step path
function getSmoothStepPath({
  sourceX,
  sourceY,
  targetX,
  targetY,
  sourcePosition = Position.Bottom,
  targetPosition = Position.Top,
}: {
  sourceX: number;
  sourceY: number;
  targetX: number;
  targetY: number;
  sourcePosition?: Position;
  targetPosition?: Position;
}) {
  const offset = 40;
  const centerX = (sourceX + targetX) / 2;
  
  // Adjust control points based on source and target positions
  let sourceControlX = sourceX;
  let sourceControlY = sourceY + offset;
  
  let targetControlX = targetX;
  let targetControlY = targetY - offset;
  
  // Create path using cubic bezier curves
  return `M${sourceX},${sourceY} C${sourceControlX},${sourceControlY} ${targetControlX},${targetControlY} ${targetX},${targetY}`;
}

// Define edge types - moved outside component to prevent recreating on each render
const edgeTypes: EdgeTypes = {};

// Flow chart component with React Flow
const FlowChart = ({ 
  graph, 
  highlightedPath = [], 
  onNodeClick 
}: { 
  graph: CFGGraph, 
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
      
      if (!sourceId || !targetId) {
        console.warn(`Invalid edge: missing source or target ID`, edge);
        return null;
      }
      
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
        // Connect from bottom of source node to top of target node
        sourceHandle: `${sourceId}-source`,
        targetHandle: `${targetId}-target`,
        // Use smooth step lines with arrowheads
        type: 'smoothstep',
        animated: isHighlighted,
        data: {
          label: edge.condition || edge.label || '',
          isHighlighted,
        },
        style: {
          stroke: isHighlighted ? '#ff7000' : '#999',
          strokeWidth: isHighlighted ? 2 : 1,
        },
      };
    }).filter(Boolean) as Edge[];
  }, [graph.edges, highlightedPath]);
  
  // Handle node click
  const handleNodeClick: NodeMouseHandler = useCallback((_, node) => {
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
  
  // Hierarchical layout algorithm
  const layoutGraph = useCallback(() => {
    if (!reactFlowInstance || flowNodes.length === 0) return;
    
    // Identify entry and exit nodes based on node type
    const entryNodes: string[] = [];
    const exitNodes: string[] = [];
    
    // Maps to track node connectivity
    const incomingEdges = new Map<string, string[]>();
    const outgoingEdges = new Map<string, string[]>();
    
    // Initialize edge maps
    flowNodes.forEach(node => {
      if (node.data.type === 'entry') {
        entryNodes.push(node.id);
      }
      if (node.data.type === 'exit') {
        exitNodes.push(node.id);
      }
      
      incomingEdges.set(node.id, []);
      outgoingEdges.set(node.id, []);
    });
    
    // Populate edge maps
    flowEdges.forEach(edge => {
      const sourceId = edge.source;
      const targetId = edge.target;
      
      if (outgoingEdges.has(sourceId)) {
        outgoingEdges.get(sourceId)!.push(targetId);
      }
      
      if (incomingEdges.has(targetId)) {
        incomingEdges.get(targetId)!.push(sourceId);
      }
    });
    
    // If no entry nodes found by type, use nodes with no incoming edges
    if (entryNodes.length === 0) {
      flowNodes.forEach(node => {
        if (incomingEdges.has(node.id) && incomingEdges.get(node.id)!.length === 0) {
          entryNodes.push(node.id);
        }
      });
    }
    
    // If still no entry nodes found, use the first node
    if (entryNodes.length === 0 && flowNodes.length > 0) {
      entryNodes.push(flowNodes[0].id);
    }
    
    // If no exit nodes found by type, use nodes with no outgoing edges
    if (exitNodes.length === 0) {
      flowNodes.forEach(node => {
        if (outgoingEdges.has(node.id) && outgoingEdges.get(node.id)!.length === 0) {
          exitNodes.push(node.id);
        }
      });
    }
    
    // Assign levels to nodes using a topological sort approach
    const levels = new Map<string, number>();
    const visited = new Set<string>();
    const queue: { id: string, level: number }[] = entryNodes.map(id => ({ id, level: 0 }));
    
    // BFS to assign initial levels
    while (queue.length > 0) {
      const { id, level } = queue.shift()!;
      
      if (visited.has(id)) {
        // Update level if we found a longer path
        if (level > (levels.get(id) || 0)) {
          levels.set(id, level);
        }
        continue;
      }
      
      visited.add(id);
      levels.set(id, level);
      
      const nextNodes = outgoingEdges.get(id) || [];
      nextNodes.forEach(nextId => {
        queue.push({ id: nextId, level: level + 1 });
      });
    }
    
    // Force exit nodes to be at the bottom
    const maxLevel = Math.max(...Array.from(levels.values()), 0);
    exitNodes.forEach(id => {
      levels.set(id, maxLevel + 1);
    });
    
    // Group nodes by level
    const nodesByLevel = new Map<number, string[]>();
    for (const [id, level] of levels.entries()) {
      if (!nodesByLevel.has(level)) {
        nodesByLevel.set(level, []);
      }
      nodesByLevel.get(level)!.push(id);
    }
    
    // Calculate positions for each node
    const nodeWidth = 180;
    const nodeHeight = 100;
    const padding = 20;
    
    const newNodes = flowNodes.map(node => {
      const level = levels.get(node.id) || 0;
      const nodesInLevel = nodesByLevel.get(level) || [];
      const indexInLevel = nodesInLevel.indexOf(node.id);
      const levelWidth = (nodesInLevel.length * nodeWidth) + ((nodesInLevel.length - 1) * padding);
      
      // Calculate X position to center nodes horizontally in their level
      const x = ((indexInLevel * nodeWidth) + (indexInLevel * padding)) - (levelWidth / 2) + (nodeWidth / 2);
      
      // Y position is determined by level
      const y = level * (nodeHeight + padding);
      
      return {
        ...node,
        position: { x, y },
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
      connectionLineType={ConnectionLineType.SmoothStep}
      defaultEdgeOptions={{
        type: 'smoothstep',
      }}
    >
      <Panel position="top-right">
        <Button size="sm" variant="outline" onClick={resetView}>
          <RefreshCw className="h-4 w-4 mr-1" />
          Reset View
        </Button>
      </Panel>
      <Controls />
      <Background color="#aaa" gap={16} />
    </ReactFlow>
  );
};

// Ensure the default graph has valid node types that match the CFGNode type
const defaultGraph: CFGGraph = { 
  nodes: [{ 
    id: 'empty', 
    label: 'No data', 
    type: 'entry' as const, 
    code: 'No code available' 
  }],
  edges: []
};

// Main ReactFlowCFGView component
const ReactFlowCFGView: React.FC<ReactFlowCFGViewProps> = ({
  originalGraph,
  ssaGraph,
  highlightedPath = [],
  onNodeClick
}) => {
  const [showSsa, setShowSsa] = useState(false);
  
  // Use default if graph is null or invalid
  const activeGraph: CFGGraph = useMemo(() => {
    if (showSsa && ssaGraph && ssaGraph.nodes && ssaGraph.nodes.length > 0) {
      return ssaGraph;
    } else if (!showSsa && originalGraph && originalGraph.nodes && originalGraph.nodes.length > 0) {
      return originalGraph;
    }
    return defaultGraph;
  }, [showSsa, originalGraph, ssaGraph]);
  
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

export default ReactFlowCFGView; 