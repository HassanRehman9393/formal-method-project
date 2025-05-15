import React, { useState } from 'react';
import { 
  Table, 
  TableBody, 
  TableCaption, 
  TableCell, 
  TableHead, 
  TableHeader, 
  TableRow 
} from "../ui/table";
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { Badge } from "../ui/badge";
import { Alert, AlertDescription, AlertTitle } from "../ui/alert";
import { 
  Info, 
  ChevronRight, 
  ChevronDown, 
  AlertCircle,
  CheckCircle
} from "lucide-react";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "../ui/tabs";
import { Button } from "../ui/button";
import { TraceStep, Counterexample } from "../../types/verification";

interface CounterexampleProps {
  counterexample: {
    variables: { [key: string]: any },
    failedAssertion?: string;
    trace?: TraceStep[];
    inputs?: Record<string, any>;
  } | null;
}

const CounterexampleDisplay: React.FC<CounterexampleProps> = ({ counterexample }) => {
  const [expandedSteps, setExpandedSteps] = useState<Record<number, boolean>>({});
  const [activeTab, setActiveTab] = useState("variables");
  
  if (!counterexample) return null;
  
  const variables = counterexample.variables || counterexample.inputs || {};
  const entries = Object.entries(variables);
  const trace = counterexample.trace || [];
  
  const toggleStep = (index: number) => {
    setExpandedSteps(prev => ({
      ...prev,
      [index]: !prev[index]
    }));
  };
  
  // Format a variable value for display
  const formatValue = (value: any): string => {
    if (value === undefined) return 'undefined';
    if (value === null) return 'null';
    
    if (typeof value === 'object') {
      if (Array.isArray(value)) {
        return `[${value.map(v => formatValue(v)).join(', ')}]`;
      }
      // Handle array-like objects from counterexample
      if (Object.keys(value).every(k => !isNaN(Number(k)))) {
        const arr = [];
        const keys = Object.keys(value).sort((a, b) => Number(a) - Number(b));
        for (const key of keys) {
          arr.push(formatValue(value[key]));
        }
        return `[${arr.join(', ')}]`;
      }
      return JSON.stringify(value);
    }
    
    return String(value);
  };

  return (
    <Card className="mb-4">
      <CardHeader className="bg-destructive/10 pb-2">
        <CardTitle className="text-lg flex items-center gap-2">
          <Badge variant="destructive">Counterexample Found</Badge>
          Verification Failed
        </CardTitle>
      </CardHeader>
      <CardContent>
        <Alert className="mb-4">
          <Info className="h-4 w-4" />
          <AlertTitle>Failed Assertion</AlertTitle>
          <AlertDescription>
            {counterexample.failedAssertion || "An assertion in the program failed with the following inputs:"}
          </AlertDescription>
        </Alert>

        <Tabs value={activeTab} onValueChange={setActiveTab}>
          <TabsList className="mb-4">
            <TabsTrigger value="variables">Variable Values</TabsTrigger>
            <TabsTrigger value="trace">Execution Trace</TabsTrigger>
          </TabsList>
          
          <TabsContent value="variables">
            <Table>
              <TableCaption>Values that cause the program to fail</TableCaption>
              <TableHeader>
                <TableRow>
                  <TableHead>Variable</TableHead>
                  <TableHead>Value</TableHead>
                  <TableHead>Type</TableHead>
                </TableRow>
              </TableHeader>
              <TableBody>
                {entries.map(([key, value]) => (
                  <TableRow key={key}>
                    <TableCell className="font-mono">{key}</TableCell>
                    <TableCell className="font-mono">{formatValue(value)}</TableCell>
                    <TableCell>{Array.isArray(value) 
                      ? "array" 
                      : typeof value}
                    </TableCell>
                  </TableRow>
                ))}
              </TableBody>
            </Table>
          </TabsContent>
          
          <TabsContent value="trace">
            {trace.length > 0 ? (
              <div className="border rounded-md">
                {trace.map((step, idx) => (
                  <div key={idx} className="border-b last:border-b-0">
                    <Button
                      variant="ghost"
                      className={`w-full flex justify-between items-center p-2 text-left ${
                        step.assertionResult === false ? 'bg-destructive/10' : ''
                      }`}
                      onClick={() => toggleStep(idx)}
                    >
                      <div className="flex items-center">
                        <span className="mr-2 w-6 text-right text-muted-foreground">
                          {step.line}:
                        </span>
                        <span className="font-mono text-sm">{step.statement}</span>
                        
                        {step.branchTaken && (
                          <Badge variant="outline" className="ml-2">
                            {step.branchTaken} branch
                          </Badge>
                        )}
                        
                        {step.assertionResult === false && (
                          <AlertCircle className="ml-2 h-4 w-4 text-destructive" />
                        )}
                        
                        {step.assertionResult === true && (
                          <CheckCircle className="ml-2 h-4 w-4 text-primary" />
                        )}
                        
                        {step.variableChanged && (
                          <Badge variant="secondary" className="ml-2">
                            {step.variableChanged} changed
                          </Badge>
                        )}
                      </div>
                      {expandedSteps[idx] ? <ChevronDown size={16} /> : <ChevronRight size={16} />}
                    </Button>
                    
                    {expandedSteps[idx] && step.state && (
                      <div className="p-3 bg-muted/50">
                        <h5 className="text-sm font-medium mb-2">Variable State</h5>
                        <div className="grid grid-cols-2 gap-2">
                          {Object.entries(step.state).map(([varName, value]) => (
                            <div key={varName} className="flex">
                              <span className="font-mono text-xs mr-2">{varName}:</span>
                              <span className="font-mono text-xs">{formatValue(value)}</span>
                            </div>
                          ))}
                        </div>
                      </div>
                    )}
                  </div>
                ))}
              </div>
            ) : (
              <Alert>
                <Info className="h-4 w-4" />
                <AlertTitle>No Trace Available</AlertTitle>
                <AlertDescription>
                  No execution trace is available for this counterexample.
                </AlertDescription>
              </Alert>
            )}
          </TabsContent>
        </Tabs>
      </CardContent>
    </Card>
  );
};

export default CounterexampleDisplay;
