import React, { useState, useEffect } from 'react';
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { Button } from "../ui/button";
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from "../ui/select";
import { Play, Pause, SkipBack, StepBack, StepForward } from "lucide-react";
// Removed the SkipForward import that was causing the warning
import { ExecutionPath } from '../../types/visualization';

interface PathHighlighterProps {
  paths: ExecutionPath[];
  onPathChange: (path: string[]) => void;
  onHighlightNode?: (nodeId: string | null) => void;
  activeNodeId?: string | null;
}

const PathHighlighter: React.FC<PathHighlighterProps> = ({ 
  paths, 
  onPathChange,
  onHighlightNode,
  activeNodeId
}) => {
  const [selectedPathId, setSelectedPathId] = useState<string>(paths[0]?.id || '');
  const [isPlaying, setIsPlaying] = useState(false);
  const [currentNodeIndex, setCurrentNodeIndex] = useState(0);
  
  const selectedPath = paths.find(p => p.id === selectedPathId);
  
  useEffect(() => {
    if (selectedPath) {
      onPathChange(selectedPath.nodes);
      setCurrentNodeIndex(0);
      if (onHighlightNode) {
        onHighlightNode(selectedPath.nodes[0] || null);
      }
    }
  }, [selectedPathId, selectedPath, onPathChange, onHighlightNode]);
  
  // Update current node index if activeNodeId changes from outside
  useEffect(() => {
    if (activeNodeId && selectedPath) {
      const index = selectedPath.nodes.indexOf(activeNodeId);
      if (index !== -1) {
        setCurrentNodeIndex(index);
      }
    }
  }, [activeNodeId, selectedPath]);
  
  useEffect(() => {
    let timeoutId: NodeJS.Timeout | null = null;
    
    if (isPlaying && selectedPath) {
      timeoutId = setTimeout(() => {
        if (currentNodeIndex < selectedPath.nodes.length - 1) {
          const nextIndex = currentNodeIndex + 1;
          setCurrentNodeIndex(nextIndex);
          if (onHighlightNode) {
            onHighlightNode(selectedPath.nodes[nextIndex]);
          }
        } else {
          setIsPlaying(false);
        }
      }, 1000);
    }
    
    return () => {
      if (timeoutId) clearTimeout(timeoutId);
    };
  }, [isPlaying, currentNodeIndex, selectedPath, onHighlightNode]);
  
  const handlePathSelect = (value: string) => {
    setSelectedPathId(value);
    setIsPlaying(false);
  };
  
  const handlePlayPause = () => {
    setIsPlaying(!isPlaying);
  };
  
  const handleReset = () => {
    setCurrentNodeIndex(0);
    setIsPlaying(false);
    if (selectedPath && onHighlightNode) {
      onHighlightNode(selectedPath.nodes[0] || null);
    }
  };
  
  const handleNext = () => {
    if (selectedPath && currentNodeIndex < selectedPath.nodes.length - 1) {
      const nextIndex = currentNodeIndex + 1;
      setCurrentNodeIndex(nextIndex);
      if (onHighlightNode) {
        onHighlightNode(selectedPath.nodes[nextIndex]);
      }
    }
  };
  
  const handlePrev = () => {
    if (selectedPath && currentNodeIndex > 0) {
      const prevIndex = currentNodeIndex - 1;
      setCurrentNodeIndex(prevIndex);
      if (onHighlightNode) {
        onHighlightNode(selectedPath.nodes[prevIndex]);
      }
    }
  };
  
  if (paths.length === 0) {
    return null;
  }
  
  return (
    <Card>
      <CardHeader className="pb-2">
        <CardTitle className="text-md">Execution Path</CardTitle>
      </CardHeader>
      <CardContent>
        <div className="flex flex-col gap-4">
          <Select value={selectedPathId} onValueChange={handlePathSelect}>
            <SelectTrigger>
              <SelectValue placeholder="Select a path" />
            </SelectTrigger>
            <SelectContent>
              {paths.map(path => (
                <SelectItem key={path.id} value={path.id}>
                  {path.name}
                </SelectItem>
              ))}
            </SelectContent>
          </Select>
          
          {selectedPath && (
            <>
              <div className="text-sm text-muted-foreground">
                {selectedPath.description}
              </div>
              
              <div className="flex items-center justify-between">
                <div className="text-sm">
                  Step {currentNodeIndex + 1} of {selectedPath.nodes.length}
                </div>
                <div className="flex gap-2">
                  <Button
                    size="icon"
                    variant="outline"
                    onClick={handleReset}
                    disabled={currentNodeIndex === 0}
                  >
                    <SkipBack className="h-4 w-4" />
                  </Button>
                  <Button
                    size="icon"
                    variant="outline"
                    onClick={handlePrev}
                    disabled={currentNodeIndex === 0}
                  >
                    <StepBack className="h-4 w-4" />
                  </Button>
                  <Button
                    size="icon"
                    variant="outline"
                    onClick={handlePlayPause}
                    disabled={currentNodeIndex === selectedPath.nodes.length - 1}
                  >
                    {isPlaying ? (
                      <Pause className="h-4 w-4" />
                    ) : (
                      <Play className="h-4 w-4" />
                    )}
                  </Button>
                  <Button
                    size="icon"
                    variant="outline"
                    onClick={handleNext}
                    disabled={currentNodeIndex === selectedPath.nodes.length - 1}
                  >
                    <StepForward className="h-4 w-4" />
                  </Button>
                </div>
              </div>
              
              <div className="h-2 w-full bg-muted rounded-full overflow-hidden">
                <div
                  className="h-full bg-primary"
                  style={{
                    width: `${(currentNodeIndex / (selectedPath.nodes.length - 1)) * 100}%`,
                    transition: 'width 0.3s ease-in-out'
                  }}
                />
              </div>
            </>
          )}
        </div>
      </CardContent>
    </Card>
  );
};

export default PathHighlighter;
