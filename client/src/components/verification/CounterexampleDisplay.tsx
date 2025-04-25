import React from 'react';
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
import { Info } from "lucide-react";

interface CounterexampleProps {
  counterexample: {
    variables: { [key: string]: any },
    failedAssertion?: string;
    trace?: { line: number; statement: string }[];
  } | null;
}

const CounterexampleDisplay: React.FC<CounterexampleProps> = ({ counterexample }) => {
  if (!counterexample) return null;
  
  const entries = Object.entries(counterexample.variables);

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
                <TableCell className="font-mono">{Array.isArray(value) 
                  ? `[${value.join(', ')}]` 
                  : String(value)}
                </TableCell>
                <TableCell>{Array.isArray(value) 
                  ? "array" 
                  : typeof value}
                </TableCell>
              </TableRow>
            ))}
          </TableBody>
        </Table>

        {counterexample.trace && counterexample.trace.length > 0 && (
          <div className="mt-4">
            <h4 className="text-sm font-medium mb-2">Execution Trace</h4>
            <div className="bg-muted p-2 rounded-md">
              <pre className="text-xs overflow-auto">
                {counterexample.trace.map((step, idx) => (
                  <div key={idx} className="py-0.5">
                    <span className="text-muted-foreground mr-2">{step.line}:</span>
                    <span>{step.statement}</span>
                  </div>
                ))}
              </pre>
            </div>
          </div>
        )}
      </CardContent>
    </Card>
  );
};

export default CounterexampleDisplay;
