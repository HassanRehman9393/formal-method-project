import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from "../ui/card";
import { Badge } from "../ui/badge";
import { CheckCircle2 } from "lucide-react";
import { 
  Table, 
  TableBody, 
  TableCaption, 
  TableCell, 
  TableHead, 
  TableHeader, 
  TableRow 
} from "../ui/table";
import { Alert, AlertDescription } from "../ui/alert";

interface SuccessVisualizationProps {
  verificationResult: {
    success: boolean;
    message: string;
    examples?: { [key: string]: any }[];
    provenProperties?: string[];
  };
}

const SuccessVisualization: React.FC<SuccessVisualizationProps> = ({ verificationResult }) => {
  if (!verificationResult?.success) return null;
  
  const { message, examples, provenProperties } = verificationResult;

  return (
    <Card className="mb-4">
      <CardHeader className="bg-green-50 dark:bg-green-950/20 pb-2">
        <CardTitle className="text-lg flex items-center gap-2">
          <CheckCircle2 className="h-5 w-5 text-green-600 dark:text-green-400" />
          <Badge variant="outline" className="bg-green-100 text-green-700 dark:bg-green-900 dark:text-green-300 border-green-200 dark:border-green-800">
            Verification Successful
          </Badge>
        </CardTitle>
      </CardHeader>
      <CardContent>
        <Alert className="mb-4 bg-green-50 dark:bg-green-950/20 border-green-200 dark:border-green-800">
          <AlertDescription className="text-green-700 dark:text-green-300">{message}</AlertDescription>
        </Alert>

        {provenProperties && provenProperties.length > 0 && (
          <div className="mb-4">
            <h4 className="text-sm font-medium mb-2">Proven Properties:</h4>
            <ul className="list-disc pl-5 space-y-1">
              {provenProperties.map((prop, idx) => (
                <li key={idx} className="text-sm">{prop}</li>
              ))}
            </ul>
          </div>
        )}

        {examples && examples.length > 0 && (
          <div className="mt-4">
            <h4 className="text-sm font-medium mb-2">Example Inputs (Program Behaves Correctly):</h4>
            <div className="overflow-x-auto">
              <Table>
                <TableCaption>Sample inputs where all assertions hold</TableCaption>
                <TableHeader>
                  <TableRow>
                    {Object.keys(examples[0]).map(key => (
                      <TableHead key={key}>{key}</TableHead>
                    ))}
                  </TableRow>
                </TableHeader>
                <TableBody>
                  {examples.map((example, idx) => (
                    <TableRow key={idx}>
                      {Object.values(example).map((value, valueIdx) => (
                        <TableCell key={valueIdx} className="font-mono">
                          {Array.isArray(value) 
                            ? `[${value.join(', ')}]` 
                            : String(value)}
                        </TableCell>
                      ))}
                    </TableRow>
                  ))}
                </TableBody>
              </Table>
            </div>
          </div>
        )}
      </CardContent>
    </Card>
  );
};

export default SuccessVisualization;
