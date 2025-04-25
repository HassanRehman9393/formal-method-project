import React from 'react';
import { Alert, AlertDescription, AlertTitle } from "../ui/alert";
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { Badge } from "../ui/badge";
import { AlertTriangle, Code, Bug } from "lucide-react";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "../ui/tabs";

interface ErrorDetailsProps {
  error: {
    type: string;
    message: string;
    line?: number;
    column?: number;
    source?: string;
    stack?: string;
    phase?: 'parsing' | 'verification' | 'ssa' | 'solver';
  };
}

const ErrorDetails: React.FC<ErrorDetailsProps> = ({ error }) => {
  if (!error) return null;
  
  const getErrorTypeIcon = () => {
    switch (error.phase) {
      case 'parsing': return <Code className="h-4 w-4" />;
      case 'solver': return <Bug className="h-4 w-4" />;
      default: return <AlertTriangle className="h-4 w-4" />;
    }
  };

  const getErrorTitle = () => {
    switch (error.phase) {
      case 'parsing': return 'Syntax Error';
      case 'verification': return 'Verification Error';
      case 'ssa': return 'Transformation Error';
      case 'solver': return 'Solver Error';
      default: return 'Error';
    }
  };

  return (
    <Card className="border-destructive/50 mb-4">
      <CardHeader className="bg-destructive/10 pb-2">
        <CardTitle className="text-lg flex items-center gap-2">
          <Badge variant="destructive">{getErrorTitle()}</Badge>
          {error.type}
        </CardTitle>
      </CardHeader>
      <CardContent className="pt-4">
        <Alert variant="destructive" className="mb-4">
          {getErrorTypeIcon()}
          <AlertTitle>{error.type}</AlertTitle>
          <AlertDescription>
            {error.message}
            {(error.line !== undefined && error.column !== undefined) && (
              <span className="block text-xs mt-1">
                at line {error.line}, column {error.column}
              </span>
            )}
          </AlertDescription>
        </Alert>

        {(error.source || error.stack) && (
          <Tabs defaultValue="error-location" className="mt-4">
            {error.source && (
              <>
                <TabsList>
                  <TabsTrigger value="error-location">Error Location</TabsTrigger>
                  {error.stack && <TabsTrigger value="stack-trace">Stack Trace</TabsTrigger>}
                </TabsList>
                <TabsContent value="error-location" className="mt-2">
                  <div className="bg-muted p-3 rounded-md overflow-x-auto">
                    <pre className="text-xs">
                      {error.source.split('\n').map((line, idx) => (
                        <div key={idx} className={`py-0.5 ${idx + 1 === error.line ? 'bg-destructive/20 font-bold' : ''}`}>
                          <span className="text-muted-foreground mr-2">{idx + 1}</span>
                          <span>{line}</span>
                          {idx + 1 === error.line && error.column && (
                            <div>
                              <span className="text-muted-foreground mr-2">{' '.repeat(String(idx + 1).length)}</span>
                              <span>{' '.repeat(error.column - 1)}^ {error.message}</span>
                            </div>
                          )}
                        </div>
                      ))}
                    </pre>
                  </div>
                </TabsContent>
              </>
            )}
            
            {error.stack && (
              <TabsContent value="stack-trace" className="mt-2">
                <div className="bg-muted p-3 rounded-md overflow-x-auto">
                  <pre className="text-xs whitespace-pre-wrap">{error.stack}</pre>
                </div>
              </TabsContent>
            )}
          </Tabs>
        )}
      </CardContent>
    </Card>
  );
};

export default ErrorDetails;
