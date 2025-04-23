import React from "react";
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";
import { Button } from "./ui/button";
import { Braces, Copy, Loader2 } from "lucide-react";
import { Badge } from "./ui/badge";
import { ScrollArea } from "./ui/scroll-area";
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from "./ui/tooltip";

interface SMTDisplayProps {
  smtCode: string;
  isLoading?: boolean;
  constraintsCount?: number;
}

const SMTDisplay: React.FC<SMTDisplayProps> = ({
  smtCode,
  isLoading = false,
  constraintsCount,
}) => {
  const [copied, setCopied] = React.useState(false);
  
  const copyToClipboard = () => {
    navigator.clipboard.writeText(smtCode);
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  };

  return (
    <Card className="border border-border/40 shadow-sm">
      <CardHeader className="pb-2 flex flex-row items-center justify-between">
        <div className="flex items-center space-x-2">
          <Braces className="h-4 w-4 text-muted-foreground" />
          <CardTitle className="text-lg font-medium">SMT Constraints</CardTitle>
        </div>
        <div className="flex items-center space-x-2">
          {constraintsCount !== undefined && smtCode && (
            <Badge variant="outline" className="text-xs">
              {constraintsCount} constraints
            </Badge>
          )}
          {smtCode && !isLoading && (
            <TooltipProvider>
              <Tooltip>
                <TooltipTrigger asChild>
                  <Button 
                    variant="ghost" 
                    size="sm" 
                    onClick={copyToClipboard}
                    className="relative h-8 group"
                  >
                    {copied ? (
                      <span className="text-xs text-green-500">Copied!</span>
                    ) : (
                      <>
                        <Copy className="h-3.5 w-3.5 mr-1.5" />
                        <span>Copy</span>
                      </>
                    )}
                  </Button>
                </TooltipTrigger>
                <TooltipContent>
                  <p>Copy SMT constraints to clipboard</p>
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
        ) : smtCode ? (
          <ScrollArea className="h-[300px]">
            <pre className="bg-muted/30 p-4 rounded-md font-mono text-sm whitespace-pre overflow-visible">
              {smtCode}
            </pre>
          </ScrollArea>
        ) : (
          <div className="flex flex-col items-center justify-center h-[200px] text-center p-6">
            <div className="rounded-full bg-muted p-3 mb-4">
              <Braces className="h-6 w-6 text-muted-foreground" />
            </div>
            <p className="text-muted-foreground">Run verification to see SMT constraints</p>
          </div>
        )}
      </CardContent>
    </Card>
  );
};

export default SMTDisplay;
