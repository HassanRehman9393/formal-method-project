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
import { DocTooltip } from "./ui/doc-tooltip";

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
          <div className="flex items-center justify-between">
            <Label htmlFor="mode" className="text-sm font-medium">
              Analysis Mode
            </Label>
            
            <DocTooltip
              content={
                <div className="space-y-2">
                  <p><strong>Verification Mode:</strong> Check assertions within a single program</p>
                  <p><strong>Equivalence Mode:</strong> Check if two programs produce the same outputs for all inputs</p>
                </div>
              }
            />
          </div>
          
          <Select 
            value={mode} 
            onValueChange={(value) => onModeChange(value as 'verification' | 'equivalence')}
          >
            <SelectTrigger className="w-full" id="mode">
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
            
            <DocTooltip
              content={
                <div className="space-y-2">
                  <p>Maximum number of times loops will be unrolled during analysis.</p>
                  <p>Higher values can find deeper bugs but may slow down verification.</p>
                  <p>Recommended range: 3-10 for most programs.</p>
                </div>
              }
            />
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
          <div className="text-xs text-muted-foreground flex items-center justify-between">
            <span>Min: 1</span>
            <span>Recommended: 5-10</span>
            <span>Max: 100</span>
          </div>
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
        
        <div className="text-xs text-muted-foreground text-center">
          <kbd className="inline-flex h-5 select-none items-center gap-1 rounded border bg-muted px-1.5 font-mono text-xs font-medium">
            Ctrl+Enter
          </kbd>
          <span className="ml-1">to run verification</span>
        </div>
      </CardContent>
    </Card>
  );
};

export default ConfigPanel;
