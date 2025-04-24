import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "./ui/tabs";
import { Alert, AlertDescription, AlertTitle } from "./ui/alert";
import { AlertCircle, CheckCircle } from "lucide-react";

// Define interfaces for parser output
interface ParseError {
  message: string;
  line: number;
  column: number;
  expectedToken?: string;
}

interface ASTNode {
  type: string;
  [key: string]: any;
}

interface ParserOutputProps {
  ast: ASTNode | null;
  parseErrors: ParseError[];
  isLoading: boolean;
}

const ParserOutputDisplay: React.FC<ParserOutputProps> = ({ 
  ast, 
  parseErrors, 
  isLoading 
}) => {
  // Recursive function to render AST nodes
  const renderASTNode = (node: ASTNode, depth = 0, key = ''): React.ReactNode => {
    if (!node) return null;
    
    return (
      <div key={key} className="ml-4 border-l-2 border-gray-200 pl-2 my-1">
        <div className="flex items-center">
          <span className="font-medium text-blue-600">{node.type}</span>
          {node.name && <span className="ml-2 text-green-600">({node.name})</span>}
          {node.value !== undefined && 
            <span className="ml-2 text-amber-600">= {typeof node.value === 'string' ? `"${node.value}"` : node.value}</span>
          }
        </div>
        
        {Object.entries(node).map(([key, value]) => {
          // Skip standard properties we've already displayed
          if (key === 'type' || key === 'name' || key === 'value') return null;
          
          // Handle arrays of nodes (like body, expressions, etc.)
          if (Array.isArray(value)) {
            return (
              <div key={key} className="ml-4 my-1">
                <span className="text-gray-500">{key}:</span>
                {value.map((item, i) => {
                  if (typeof item === 'object' && item !== null) {
                    return renderASTNode(item, depth + 1, `${key}-${i}`);
                  }
                  return <div key={`${key}-${i}`} className="ml-4">{String(item)}</div>;
                })}
              </div>
            );
          }
          
          // Handle nested objects which are AST nodes
          if (typeof value === 'object' && value !== null && value.type) {
            return (
              <div key={key} className="my-1">
                <span className="text-gray-500">{key}:</span>
                {renderASTNode(value, depth + 1, key)}
              </div>
            );
          }
          
          // Handle primitive properties
          if (value !== null && value !== undefined && typeof value !== 'function') {
            return (
              <div key={key} className="ml-4 my-1">
                <span className="text-gray-500">{key}:</span> {String(value)}
              </div>
            );
          }
          
          return null;
        })}
      </div>
    );
  };

  return (
    <Card className="w-full">
      <CardHeader>
        <CardTitle>Parser Output</CardTitle>
      </CardHeader>
      <CardContent>
        <Tabs defaultValue="ast">
          <TabsList>
            <TabsTrigger value="ast">Abstract Syntax Tree</TabsTrigger>
            <TabsTrigger value="errors">Parsing Errors</TabsTrigger>
          </TabsList>
          
          <TabsContent value="ast">
            {isLoading ? (
              <div className="flex justify-center p-4">
                <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-700"></div>
              </div>
            ) : ast ? (
              <div className="bg-gray-50 p-4 rounded-md overflow-auto max-h-[500px]">
                <div className="font-mono text-sm">{renderASTNode(ast, 0, 'root')}</div>
              </div>
            ) : (
              <div className="text-center p-4 text-gray-500">
                No parse tree available. Please parse a valid program first.
              </div>
            )}
          </TabsContent>
          
          <TabsContent value="errors">
            {isLoading ? (
              <div className="flex justify-center p-4">
                <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-700"></div>
              </div>
            ) : parseErrors.length > 0 ? (
              <div className="space-y-2">
                {parseErrors.map((error, idx) => (
                  <Alert key={idx} variant="destructive">
                    <AlertCircle className="h-4 w-4" />
                    <AlertTitle>Parse Error at line {error.line}, column {error.column}</AlertTitle>
                    <AlertDescription>
                      {error.message}
                      {error.expectedToken && (
                        <div className="mt-1">Expected: {error.expectedToken}</div>
                      )}
                    </AlertDescription>
                  </Alert>
                ))}
              </div>
            ) : (
              <Alert>
                <CheckCircle className="h-4 w-4 text-green-500" />
                <AlertTitle>Success</AlertTitle>
                <AlertDescription>
                  No parsing errors found.
                </AlertDescription>
              </Alert>
            )}
          </TabsContent>
        </Tabs>
      </CardContent>
    </Card>
  );
};

export default ParserOutputDisplay;
