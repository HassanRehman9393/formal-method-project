import React from "react";
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";
import { Label } from "./ui/label";
import { Input } from "./ui/input";
import { Button } from "./ui/button";
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from "./ui/select";
import { Separator } from "./ui/separator";
import { 
  Settings, 
  CheckCircle2, 
  GitCompare, 
  Infinity, 
  Play 
} from "lucide-react";
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from "./ui/tooltip";

interface ConfigPanelProps {
  mode: 'verification' | 'equivalence';
  onModeChange: (mode: 'verification' | 'equivalence') => void;
  loopUnrollingDepth: number;
  onLoopUnrollingDepthChange: (depth: number) => void;
  onVerify: () => void;
  isProcessing?: boolean;
}

const ConfigPanel: React.FC<ConfigPanelProps> = ({
  mode,
  onModeChange,
  loopUnrollingDepth,
  onLoopUnrollingDepthChange,
  onVerify,
  isProcessing = false,
}) => {
  return (
    <Card className="border border-border/40 shadow-sm">
      <CardHeader className="pb-3">
        <div className="flex items-center space-x-2">
          <Settings className="h-4 w-4 text-muted-foreground" />
          <CardTitle className="text-lg font-medium">Configuration</CardTitle>
        </div>
      </CardHeader>

      <CardContent className="space-y-6">
        <div className="space-y-3">
          <Label htmlFor="mode" className="text-sm font-medium">
            Analysis Mode
          </Label>
          <Select 
            value={mode} 
            onValueChange={(value) => onModeChange(value as 'verification' | 'equivalence')}
          >
            <SelectTrigger className="w-full">
              <SelectValue placeholder="Select mode" />
            </SelectTrigger>
            <SelectContent>
              <SelectItem value="verification" className="flex items-center">
                <div className="flex items-center">
                  <CheckCircle2 className="mr-2 h-4 w-4 text-primary" />
                  <span>Verification</span>
                </div>
              </SelectItem>
              <SelectItem value="equivalence" className="flex items-center">
                <div className="flex items-center">
                  <GitCompare className="mr-2 h-4 w-4 text-primary" />
                  <span>Equivalence</span>
                </div>
              </SelectItem>
            </SelectContent>
          </Select>
          <p className="text-xs text-muted-foreground mt-1">
            {mode === 'verification' 
              ? 'Verify assertions in a single program' 
              : 'Check if two programs are semantically equivalent'}
          </p>
        </div>

        <Separator />

        <div className="space-y-3">
          <div className="flex items-center justify-between">
            <Label htmlFor="loopUnrollingDepth" className="text-sm font-medium">
              Loop Unrolling Depth
            </Label>
            <TooltipProvider>
              <Tooltip>
                <TooltipTrigger asChild>
                  <div className="rounded-full bg-muted flex items-center justify-center h-5 w-5">
                    <Infinity className="h-3 w-3 text-muted-foreground" />
                  </div>
                </TooltipTrigger>
                <TooltipContent side="top">
                  <p className="max-w-xs text-xs">
                    Maximum number of iterations to unroll loops for verification. 
                    Higher values increase analysis precision but may slow down verification.
                  </p>
                </TooltipContent>
              </Tooltip>
            </TooltipProvider>
          </div>
          <Input 
            id="loopUnrollingDepth"
            type="number"
            min={1}
            max={100}
            value={loopUnrollingDepth}
            onChange={(e) => onLoopUnrollingDepthChange(parseInt(e.target.value) || 1)}
            className="h-9"
          />
        </div>

        <Button 
          className="w-full mt-4" 
          onClick={onVerify}
          disabled={isProcessing}
        >
          {isProcessing ? (
            <>
              <div className="mr-2 animate-spin h-4 w-4 border-2 border-primary border-t-transparent rounded-full" />
              Processing...
            </>
          ) : (
            <>
              <Play className="mr-2 h-4 w-4" />
              {mode === 'verification' ? 'Verify Program' : 'Check Equivalence'}
            </>
          )}
        </Button>
      </CardContent>
    </Card>
  );
};

export default ConfigPanel;
