import React from "react";
import { Alert, AlertDescription, AlertTitle } from "./alert";
import { Button } from "./button";
import { AlertTriangle, X, RefreshCw } from "lucide-react";
import type { ErrorDetails } from "../../contexts/VerificationContext";

interface ErrorDisplayProps {
  error: ErrorDetails;
  onDismiss?: () => void;
  onRetry?: () => void;
}

export function ErrorDisplay({ error, onDismiss, onRetry }: ErrorDisplayProps) {
  const errorTypeToTitle = {
    parser: "Parsing Error",
    transformer: "Transformation Error",
    solver: "Solver Error",
    network: "Network Error",
    generic: "Error",
  };
  
  const title = errorTypeToTitle[error.type] || "Error";
  
  return (
    <Alert variant="destructive" className="relative">
      <AlertTriangle className="h-4 w-4" />
      <AlertTitle className="font-medium">{title}</AlertTitle>
      <AlertDescription className="mt-2">
        <p>{error.message}</p>
        {error.details && (
          <pre className="mt-2 whitespace-pre-wrap text-xs p-2 bg-destructive/20 rounded">
            {error.details}
          </pre>
        )}
        {(error.line !== undefined && error.column !== undefined) && (
          <p className="mt-2 text-xs">
            Line {error.line}, Column {error.column}
          </p>
        )}
      </AlertDescription>
      
      <div className="absolute top-2 right-2 flex space-x-2">
        {onRetry && (
          <Button 
            size="icon" 
            variant="outline" 
            className="h-6 w-6" 
            onClick={onRetry}
          >
            <RefreshCw className="h-3 w-3" />
            <span className="sr-only">Retry</span>
          </Button>
        )}
        {onDismiss && (
          <Button 
            size="icon" 
            variant="outline" 
            className="h-6 w-6" 
            onClick={onDismiss}
          >
            <X className="h-3 w-3" />
            <span className="sr-only">Dismiss</span>
          </Button>
        )}
      </div>
    </Alert>
  );
}
