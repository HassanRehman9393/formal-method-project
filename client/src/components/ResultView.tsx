import React from "react";
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";
import { Alert, AlertDescription, AlertTitle } from "./ui/alert";
import { 
  CheckCircle2, 
  XCircle, 
  AlertCircle, 
  Clock, 
  FileJson, 
  Eye
} from "lucide-react";
import { Badge } from "./ui/badge";
import { Button } from "./ui/button";
import { Collapsible, CollapsibleContent, CollapsibleTrigger } from "./ui/collapsible";
import { ScrollArea } from "./ui/scroll-area";

type ResultStatus = 'success' | 'failure' | 'error' | 'pending' | null;

interface ResultViewProps {
  status: ResultStatus;
  message?: string;
  counterexample?: Record<string, any>;
  executionTime?: number;
}

const ResultView: React.FC<ResultViewProps> = ({
  status,
  message = "",
  counterexample,
  executionTime = 0,
}) => {
  const [isOpen, setIsOpen] = React.useState(false);

  if (status === null) {
    return (
      <Card className="border border-border/40 shadow-sm">
        <CardHeader className="pb-2">
          <div className="flex items-center space-x-2">
            <AlertCircle className="h-4 w-4 text-muted-foreground" />
            <CardTitle className="text-lg font-medium">Results</CardTitle>
          </div>
        </CardHeader>
        <CardContent>
          <div className="flex flex-col items-center justify-center p-8 text-center">
            <div className="rounded-full bg-muted p-3 mb-4">
              <Eye className="h-6 w-6 text-muted-foreground" />
            </div>
            <p className="text-muted-foreground">Run verification to see results</p>
          </div>
        </CardContent>
      </Card>
    );
  }

  if (status === 'pending') {
    return (
      <Card className="border border-border/40 shadow-sm">
        <CardHeader className="pb-2">
          <div className="flex items-center justify-between">
            <div className="flex items-center space-x-2">
              <Clock className="h-4 w-4 text-muted-foreground" />
              <CardTitle className="text-lg font-medium">Processing...</CardTitle>
            </div>
            <Badge variant="outline" className="text-xs">Analyzing</Badge>
          </div>
        </CardHeader>
        <CardContent>
          <div className="flex flex-col items-center justify-center p-8">
            <div className="flex items-center justify-center mb-4">
              <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-primary"></div>
            </div>
            <p className="text-muted-foreground">Performing verification analysis</p>
          </div>
        </CardContent>
      </Card>
    );
  }

  const statusConfig = {
    success: {
      icon: <CheckCircle2 className="h-5 w-5 text-green-500" />,
      title: "Verification Successful",
      badge: <Badge className="bg-green-500/20 text-green-700 hover:bg-green-500/20 border-0">Valid</Badge>,
      alertClass: "border-green-500/40 bg-green-500/10 text-green-700"
    },
    failure: {
      icon: <XCircle className="h-5 w-5 text-red-500" />,
      title: "Verification Failed",
      badge: <Badge className="bg-red-500/20 text-red-700 hover:bg-red-500/20 border-0">Invalid</Badge>,
      alertClass: "border-red-500/40 bg-red-500/10 text-red-700"
    },
    error: {
      icon: <AlertCircle className="h-5 w-5 text-amber-500" />,
      title: "Error",
      badge: <Badge className="bg-amber-500/20 text-amber-700 hover:bg-amber-500/20 border-0">Error</Badge>,
      alertClass: "border-amber-500/40 bg-amber-500/10 text-amber-700"
    }
  };

  const currentStatus = statusConfig[status];

  return (
    <Card className="border border-border/40 shadow-sm">
      <CardHeader className="pb-2">
        <div className="flex items-center justify-between">
          <div className="flex items-center space-x-2">
            {currentStatus.icon}
            <CardTitle className="text-lg font-medium">{currentStatus.title}</CardTitle>
          </div>
          <div className="flex items-center space-x-2">
            {currentStatus.badge}
            {executionTime > 0 && (
              <Badge variant="outline" className="text-xs">
                {executionTime}ms
              </Badge>
            )}
          </div>
        </div>
      </CardHeader>
      <CardContent className="space-y-4">
        <Alert className={currentStatus.alertClass}>
          <AlertTitle className="mb-1 flex items-center gap-2">
            {currentStatus.icon}
            <span>{currentStatus.title}</span>
          </AlertTitle>
          <AlertDescription className="text-sm">{message}</AlertDescription>
        </Alert>

        {counterexample && (
          <Collapsible 
            open={isOpen} 
            onOpenChange={setIsOpen}
            className="border rounded-md overflow-hidden"
          >
            <div className="flex items-center justify-between p-3 bg-muted/50">
              <div className="flex items-center space-x-2 text-sm font-medium">
                <FileJson className="h-4 w-4 text-muted-foreground" />
                <span>Counterexample</span>
              </div>
              <CollapsibleTrigger asChild>
                <Button variant="ghost" size="sm">
                  {isOpen ? "Hide details" : "Show details"}
                </Button>
              </CollapsibleTrigger>
            </div>
            <CollapsibleContent>
              <ScrollArea className="max-h-[200px]">
                <pre className="bg-muted/30 text-xs p-3 overflow-auto m-0">
                  {JSON.stringify(counterexample, null, 2)}
                </pre>
              </ScrollArea>
            </CollapsibleContent>
          </Collapsible>
        )}
      </CardContent>
    </Card>
  );
};

export default ResultView;
