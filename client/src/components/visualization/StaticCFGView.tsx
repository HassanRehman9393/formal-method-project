import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { Switch } from "../ui/switch";
import { Label } from "../ui/label";
import { CFGNode, CFGEdge } from "../../types/visualization";

interface StaticCFGViewProps {
  originalGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  ssaGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  onNodeClick?: (nodeId: string) => void;
}

const StaticCFGView: React.FC<StaticCFGViewProps> = ({
  originalGraph,
  ssaGraph,
  onNodeClick
}) => {
  const [showSsa, setShowSsa] = React.useState(false);
  
  // Create a default empty graph to avoid null issues
  const defaultGraph = { 
    nodes: [{ id: 'empty', label: 'No data', type: 'entry', code: 'No code available' }],
    edges: []
  };
  
  // Use default if graph is null or invalid
  const activeGraph = showSsa 
    ? (ssaGraph && ssaGraph.nodes && ssaGraph.nodes.length > 0 ? ssaGraph : defaultGraph) 
    : (originalGraph && originalGraph.nodes && originalGraph.nodes.length > 0 ? originalGraph : defaultGraph);

  // Generate a simple table view of nodes and edges
  const renderNodesTable = () => (
    <div className="overflow-auto max-h-[300px] border rounded-md p-2 mb-4">
      <table className="w-full text-sm">
        <thead className="bg-muted font-medium">
          <tr>
            <th className="text-left p-2">ID</th>
            <th className="text-left p-2">Label</th>
            <th className="text-left p-2">Type</th>
          </tr>
        </thead>
        <tbody>
          {activeGraph.nodes.map(node => (
            <tr 
              key={node.id} 
              className="hover:bg-muted/50 cursor-pointer"
              onClick={() => onNodeClick && onNodeClick(node.id)}
            >
              <td className="p-2">{node.id}</td>
              <td className="p-2">{node.label}</td>
              <td className="p-2">{node.type}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );

  const renderEdgesTable = () => (
    <div className="overflow-auto max-h-[300px] border rounded-md p-2">
      <table className="w-full text-sm">
        <thead className="bg-muted font-medium">
          <tr>
            <th className="text-left p-2">Source</th>
            <th className="text-left p-2">Target</th>
            <th className="text-left p-2">Label/Condition</th>
          </tr>
        </thead>
        <tbody>
          {activeGraph.edges.map((edge, index) => (
            <tr key={index} className="hover:bg-muted/50">
              <td className="p-2">{typeof edge.source === 'string' ? edge.source : edge.source.id}</td>
              <td className="p-2">{typeof edge.target === 'string' ? edge.target : edge.target.id}</td>
              <td className="p-2">{edge.condition || edge.label || ""}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );

  return (
    <Card className="w-full">
      <CardHeader className="pb-2">
        <div className="flex items-center justify-between">
          <CardTitle>Control Flow Graph (Static View)</CardTitle>
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
        <div className="space-y-4">
          <div className="p-4 text-center bg-muted/20 rounded-md mb-4">
            <p className="text-muted-foreground">
              Using simplified static view due to visualization error.
            </p>
          </div>
          
          <h3 className="text-lg font-medium">Nodes</h3>
          {renderNodesTable()}
          
          <h3 className="text-lg font-medium">Edges</h3>
          {renderEdgesTable()}
        </div>
      </CardContent>
    </Card>
  );
};

export default StaticCFGView; 