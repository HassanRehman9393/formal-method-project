import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Alert, AlertDescription, AlertTitle } from './ui/alert';
import { Badge } from './ui/badge';
import { Separator } from './ui/separator';
import { CheckCircle, AlertTriangle, XCircle, Clock } from 'lucide-react';
import { ResultStatus } from '../contexts/VerificationContext';

interface CounterexampleTrace {
  line: number;
  state: Record<string, any>;
}

interface Counterexample {
  inputs: Record<string, any>;
  outputs?: Record<string, any>;
  path?: string[];
  trace?: CounterexampleTrace[];
}

export interface ResultViewProps {
  status: ResultStatus;
  message: string;
  counterexample?: Counterexample;
  executionTime: number;
}

const ResultView: React.FC<ResultViewProps> = ({
  status,
  message,
  counterexample,
  executionTime,
}) => {
  // Icon and alert variant based on status
  const getStatusConfig = () => {
    switch (status) {
      case 'success':
        return {
          icon: <CheckCircle className="h-5 w-5 text-green-500" />,
          variant: 'default',
          title: 'Verification Successful',
          badgeClass: 'bg-green-100 text-green-800',
          badgeText: 'Success',
        };
      case 'failure':
        return {
          icon: <AlertTriangle className="h-5 w-5 text-amber-500" />,
          variant: 'warning',
          title: 'Verification Failed',
          badgeClass: 'bg-amber-100 text-amber-800',
          badgeText: 'Failed',
        };
      case 'error':
        return {
          icon: <XCircle className="h-5 w-5 text-red-500" />,
          variant: 'destructive',
          title: 'Error Occurred',
          badgeClass: 'bg-red-100 text-red-800',
          badgeText: 'Error',
        };
      default:
        return {
          icon: <Clock className="h-5 w-5 text-gray-500" />,
          variant: 'default',
          title: 'No Results',
          badgeClass: 'bg-gray-100 text-gray-800',
          badgeText: 'Pending',
        };
    }
  };

  const statusConfig = getStatusConfig();

  // Format execution time nicely
  const formattedTime = executionTime > 1000 
    ? `${(executionTime / 1000).toFixed(2)} seconds` 
    : `${executionTime} milliseconds`;

  return (
    <Card>
      <CardHeader className="pb-2">
        <div className="flex justify-between items-center">
          <CardTitle className="flex items-center">
            {statusConfig.icon}
            <span className="ml-2">{statusConfig.title}</span>
          </CardTitle>
          <Badge className={statusConfig.badgeClass}>
            {statusConfig.badgeText}
          </Badge>
        </div>
      </CardHeader>
      <CardContent>
        {/* Main message */}
        <Alert variant={statusConfig.variant as any}>
          <AlertTitle>Result</AlertTitle>
          <AlertDescription>{message}</AlertDescription>
        </Alert>

        {/* Execution time */}
        <div className="mt-4 text-sm text-muted-foreground flex items-center">
          <Clock className="h-4 w-4 mr-1" />
          Execution time: {formattedTime}
        </div>

        {/* Counterexample section */}
        {counterexample && (
          <div className="mt-4">
            <Separator className="my-4" />
            <h4 className="font-medium mb-2">Counterexample</h4>
            
            {/* Input values */}
            <div className="mb-3">
              <h5 className="text-sm font-medium text-muted-foreground mb-1">Inputs:</h5>
              <div className="bg-muted p-2 rounded overflow-x-auto">
                <pre className="text-xs">
                  {JSON.stringify(counterexample.inputs, null, 2)}
                </pre>
              </div>
            </div>
            
            {/* Output values if they exist */}
            {counterexample.outputs && (
              <div className="mb-3">
                <h5 className="text-sm font-medium text-muted-foreground mb-1">Outputs:</h5>
                <div className="bg-muted p-2 rounded overflow-x-auto">
                  <pre className="text-xs">
                    {JSON.stringify(counterexample.outputs, null, 2)}
                  </pre>
                </div>
              </div>
            )}
            
            {/* Execution trace if it exists */}
            {counterexample.trace && counterexample.trace.length > 0 && (
              <div>
                <h5 className="text-sm font-medium text-muted-foreground mb-1">Execution Trace:</h5>
                <div className="border rounded divide-y">
                  <div className="grid grid-cols-4 bg-muted p-2 text-xs font-medium">
                    <div>Step</div>
                    <div>Line</div>
                    <div className="col-span-2">State</div>
                  </div>
                  {counterexample.trace.map((step, index) => (
                    <div key={index} className="grid grid-cols-4 p-2 text-xs">
                      <div>{index + 1}</div>
                      <div>{step.line}</div>
                      <div className="col-span-2 overflow-x-auto">
                        <pre>{JSON.stringify(step.state, null, 2)}</pre>
                      </div>
                    </div>
                  ))}
                </div>
              </div>
            )}
          </div>
        )}
      </CardContent>
    </Card>
  );
};

export default ResultView;
