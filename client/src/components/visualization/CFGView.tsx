import React, { useEffect, useRef, useState } from 'react';
import * as d3 from 'd3';
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { Switch } from "../ui/switch";
import { Label } from "../ui/label";
import { Button } from "../ui/button";
import { ZoomIn, ZoomOut, RotateCw, Maximize } from "lucide-react";
import { CFGNode, CFGEdge } from "../../types/visualization";

interface CFGViewProps {
  originalGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  ssaGraph?: { nodes: CFGNode[]; edges: CFGEdge[] } | null;
  highlightedPath?: string[];
  onNodeClick?: (nodeId: string) => void;
}

const CFGView: React.FC<CFGViewProps> = ({ 
  originalGraph, 
  ssaGraph, 
  highlightedPath = [],
  onNodeClick 
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [showSsa, setShowSsa] = useState(false);
  const [zoom, setZoom] = useState<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(null);
  
  const activeGraph = showSsa ? ssaGraph : originalGraph;

  useEffect(() => {
    if (!svgRef.current || !activeGraph || !activeGraph.nodes.length) return;

    const width = svgRef.current.clientWidth;
    const height = 600;

    // Clear previous graph
    d3.select(svgRef.current).selectAll("*").remove();

    const svg = d3.select(svgRef.current)
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height])
      .attr("style", "max-width: 100%; height: auto;");

    // Create zoom behavior
    const zoomBehavior = d3.zoom<SVGSVGElement, unknown>()
      .extent([[0, 0], [width, height]])
      .scaleExtent([0.1, 4])
      .on("zoom", (event) => {
        g.attr("transform", event.transform);
      });

    // Apply zoom behavior to svg
    svg.call(zoomBehavior);
    setZoom(zoomBehavior);

    // Create container for the graph
    const g = svg.append("g");

    // Create simulation for force-directed layout
    const simulation = d3.forceSimulation<CFGNode>(activeGraph.nodes)
      .force("link", d3.forceLink<CFGNode, CFGEdge>(activeGraph.edges)
        .id(d => d.id)
        .distance(150))
      .force("charge", d3.forceManyBody().strength(-1000))
      .force("center", d3.forceCenter(width / 2, height / 2))
      .force("x", d3.forceX(width / 2).strength(0.1))
      .force("y", d3.forceY(height / 2).strength(0.1));

    // Create edges
    const edge = g.append("g")
      .attr("stroke", "#999")
      .attr("stroke-opacity", 0.6)
      .selectAll("g")
      .data(activeGraph.edges)
      .join("g");

    // Add path for edges
    const path = edge.append("path")
      .attr("stroke-width", d => d.isHighlighted ? 3 : 1.5)
      .attr("stroke", d => d.isHighlighted ? "#ff7000" : "#999")
      .attr("marker-end", "url(#arrowhead)");

    // Add edge labels
    edge.append("text")
      .attr("font-size", 10)
      .attr("text-anchor", "middle")
      .attr("dy", -5)
      .text(d => d.condition || d.label || "")
      .attr("fill", "#666");

    // Create arrow marker
    svg.append("defs").append("marker")
      .attr("id", "arrowhead")
      .attr("viewBox", "0 -5 10 10")
      .attr("refX", 20)
      .attr("refY", 0)
      .attr("markerWidth", 6)
      .attr("markerHeight", 6)
      .attr("orient", "auto")
      .append("path")
      .attr("fill", "#999")
      .attr("d", "M0,-5L10,0L0,5");

    // Create nodes
    const node = g.append("g")
      .selectAll("g")
      .data(activeGraph.nodes)
      .join("g")
      // Use 'as any' to avoid TypeScript errors with D3's drag behavior
      .call((selection) => drag(simulation)(selection as any))
      .on("click", function(_, d) {
        if (onNodeClick) onNodeClick(d.id);
        
        // Toggle highlighting state
        d3.select(this).select("circle")
          .transition()
          .duration(200)
          .attr("stroke-width", 3)
          .attr("stroke", "#ff7000");

        setTimeout(() => {
          d3.select(this).select("circle")
            .transition()
            .duration(200)
            .attr("stroke-width", d.isHighlighted ? 2 : 1.5)
            .attr("stroke", d.isHighlighted ? "#ff7000" : "#666");
        }, 500);
      });

    // Add circle for nodes with different colors based on type
    node.append("circle")
      .attr("r", 20)
      .attr("fill", d => {
        switch (d.type) {
          case 'entry': return "#c8e6c9"; // light green
          case 'exit': return "#ffccbc"; // light red
          case 'condition': return "#bbdefb"; // light blue
          case 'join': return "#e1bee7"; // light purple
          default: return "#f5f5f5"; // light gray
        }
      })
      .attr("stroke", d => d.isHighlighted || highlightedPath.includes(d.id) ? "#ff7000" : "#666")
      .attr("stroke-width", d => d.isHighlighted || highlightedPath.includes(d.id) ? 2 : 1.5);

    // Add node labels
    node.append("text")
      .attr("text-anchor", "middle")
      .attr("dy", 5)
      .attr("font-size", "10px")
      .text(d => {
        // Truncate long labels
        const displayText = d.label || d.id;
        return displayText.length > 12 ? displayText.substring(0, 10) + "..." : displayText;
      });

    // Add tooltips for nodes
    node.append("title")
      .text(d => `${d.label || d.id}\n${d.code}`);

    // Update positions on simulation tick
    simulation.on("tick", () => {
      path.attr("d", linkArc);
      node.attr("transform", (d: CFGNode) => `translate(${d.x || 0},${d.y || 0})`);
      edge.selectAll("text")
        .attr("x", (d: any) => {
          const source = typeof d.source === 'string' ? {x: 0} : d.source;
          const target = typeof d.target === 'string' ? {x: 0} : d.target;
          return ((source.x || 0) + (target.x || 0)) / 2;
        })
        .attr("y", (d: any) => {
          const source = typeof d.source === 'string' ? {y: 0} : d.source;
          const target = typeof d.target === 'string' ? {y: 0} : d.target;
          return ((source.y || 0) + (target.y || 0)) / 2;
        });
    });

    // Stabilize simulation
    for (let i = 0; i < 300; ++i) simulation.tick();
    simulation.alpha(0.3).restart();

    // Cleanup
    return () => {
      simulation.stop();
    };
  }, [activeGraph, showSsa, highlightedPath, onNodeClick]);

  // Helper function for drag behavior
  function drag(simulation: d3.Simulation<CFGNode, undefined>) {
    const dragBehavior = d3.drag<SVGGElement, CFGNode>()
      .on("start", (event: any) => {
        if (!event.active) simulation.alphaTarget(0.3).restart();
        event.subject.fx = event.subject.x;
        event.subject.fy = event.subject.y;
      })
      .on("drag", (event: any) => {
        event.subject.fx = event.x;
        event.subject.fy = event.y;
      })
      .on("end", (event: any) => {
        if (!event.active) simulation.alphaTarget(0);
        event.subject.fx = null;
        event.subject.fy = null;
      });
    
    return dragBehavior;
  }

  // Helper function for curved edge paths
  function linkArc(d: any) {
    const source = typeof d.source === 'string' ? {x: 0, y: 0} : d.source;
    const target = typeof d.target === 'string' ? {x: 0, y: 0} : d.target;
    
    const dx = (target.x || 0) - (source.x || 0);
    const dy = (target.y || 0) - (source.y || 0);
    const dr = Math.sqrt(dx * dx + dy * dy);
    return `M${source.x || 0},${source.y || 0}A${dr},${dr} 0 0,1 ${target.x || 0},${target.y || 0}`;
  }

  const handleZoomIn = () => {
    if (zoom && svgRef.current) {
      zoom.scaleBy(d3.select(svgRef.current), 1.2);
    }
  };

  const handleZoomOut = () => {
    if (zoom && svgRef.current) {
      zoom.scaleBy(d3.select(svgRef.current), 1 / 1.2);
    }
  };

  const handleReset = () => {
    if (zoom && svgRef.current) {
      d3.select(svgRef.current)
        .transition()
        .duration(750)
        .call(zoom.transform, d3.zoomIdentity);
    }
  };

  const handleFitContent = () => {
    if (zoom && svgRef.current) {
      const svg = d3.select(svgRef.current);
      // Cast the node to SVGGraphicsElement to access getBBox
      const gNode = svg.select("g").node() as SVGGraphicsElement | null;
      const bounds = gNode?.getBBox();
      
      if (bounds) {
        const width = svgRef.current.clientWidth;
        const height = 600;
        const scale = 0.95 / Math.max(
          bounds.width / width,
          bounds.height / height
        );
        const translateX = width / 2 - scale * (bounds.x + bounds.width / 2);
        const translateY = height / 2 - scale * (bounds.y + bounds.height / 2);

        svg.transition()
          .duration(750)
          .call(zoom.transform, d3.zoomIdentity
            .translate(translateX, translateY)
            .scale(scale)
          );
      }
    }
  };

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
        <div className="flex mb-2 gap-2">
          <Button size="sm" variant="outline" onClick={handleZoomIn}>
            <ZoomIn className="h-4 w-4 mr-1" />
            Zoom In
          </Button>
          <Button size="sm" variant="outline" onClick={handleZoomOut}>
            <ZoomOut className="h-4 w-4 mr-1" />
            Zoom Out
          </Button>
          <Button size="sm" variant="outline" onClick={handleReset}>
            <RotateCw className="h-4 w-4 mr-1" />
            Reset
          </Button>
          <Button size="sm" variant="outline" onClick={handleFitContent}>
            <Maximize className="h-4 w-4 mr-1" />
            Fit
          </Button>
        </div>
        <div className="border rounded-md bg-background">
          {activeGraph ? (
            <svg ref={svgRef} className="w-full h-[600px]" />
          ) : (
            <div className="flex items-center justify-center h-[600px] text-muted-foreground">
              No control flow graph available
            </div>
          )}
        </div>
      </CardContent>
    </Card>
  );
};

export default CFGView;
