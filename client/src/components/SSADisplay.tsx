import React from "react";
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";
import { Code, Copy, Loader2 } from "lucide-react";
import { Button } from "./ui/button";
import { Badge } from "./ui/badge";
import { ScrollArea } from "./ui/scroll-area";
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from "./ui/tooltip";

interface SSADisplayProps {
  ssaCode: string;
  isLoading?: boolean;
  title?: string;
  optimized?: boolean;
}

const SSADisplay: React.FC<SSADisplayProps> = ({
  ssaCode,
  isLoading = false,
  title = "SSA Representation",
  optimized = false,
}) => {
  const copyToClipboard = () => {
    navigator.clipboard.writeText(ssaCode);
  };

  return (
    <Card className="border border-border/40 shadow-sm">
      <CardHeader className="pb-2 flex flex-row items-center justify-between">
        <div className="flex items-center space-x-2">
          <Code className="h-4 w-4 text-muted-foreground" />
          <CardTitle className="text-lg font-medium">{title}</CardTitle>
        </div>
        <div className="flex items-center space-x-2">
          {optimized && (
            <Badge className="bg-blue-500/20 text-blue-700 hover:bg-blue-500/20 border-0 text-xs">
              Optimized
            </Badge>
          )}
          {ssaCode && !isLoading && (
            <TooltipProvider>
              <Tooltip>
                <TooltipTrigger asChild>
                  <Button 
                    variant="ghost" 
                    size="sm" 
                    onClick={copyToClipboard} 
                    className="h-8 w-8 p-0"
                  >
                    <Copy className="h-3.5 w-3.5" />
                    <span className="sr-only">Copy code</span>
                  </Button>
                </TooltipTrigger>
                <TooltipContent>
                  <p>Copy to clipboard</p>
                </TooltipContent>
              </Tooltip>
            </TooltipProvider>
          )}
        </div>
      </CardHeader>

      <CardContent>
        {isLoading ? (
          <div className="flex items-center justify-center h-[200px]">
            <Loader2 className="h-8 w-8 animate-spin text-primary" />
          </div>
        ) : ssaCode ? (
          <ScrollArea className="h-[300px]">
            <pre className="bg-muted/30 p-4 rounded-md font-mono text-sm whitespace-pre overflow-visible">
              {ssaCode}
            </pre>
          </ScrollArea>
        ) : (
          <div className="flex flex-col items-center justify-center h-[200px] text-center p-6">
            <div className="rounded-full bg-muted p-3 mb-4">
              <Code className="h-6 w-6 text-muted-foreground" />
            </div>
            <p className="text-muted-foreground">Run verification to see SSA representation</p>
          </div>
        )}
      </CardContent>
    </Card>
  );
};

export default SSADisplay;
