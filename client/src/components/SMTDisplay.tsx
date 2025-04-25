import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Badge } from './ui/badge';
import { Button } from './ui/button';
import { Copy } from 'lucide-react';
import { LoadingState } from './ui/loading-state';
import CodeMirror from '@uiw/react-codemirror';
import { EditorView } from '@codemirror/view';
import { StreamLanguage } from '@codemirror/language';

// Simple language definition for SMT-LIB2
const smtLibLanguage = StreamLanguage.define({
  name: 'smtlib2',
  token(stream) { // Removed the unused 'state' parameter
    if (stream.eatSpace()) return null;
    
    // Comments
    if (stream.match(';')) {
      stream.skipToEnd();
      return 'comment';
    }
    
    // Strings
    if (stream.match(/"([^"\\]|\\.)*"/)) return 'string';
    
    // Keywords
    if (stream.match(/(declare-const|declare-fun|assert|check-sat|get-model|set-logic|define-fun)/)) {
      return 'keyword';
    }
    
    // Types
    if (stream.match(/(Int|Bool|Real|Array)/)) return 'type';
    
    // Operators
    if (stream.match(/[\+\-\*\/=<>!&|]+/)) return 'operator';
    
    // Parentheses
    if (stream.match(/[\(\)]/)) return 'bracket';
    
    // Numbers
    if (stream.match(/\d+(\.\d+)?/)) return 'number';
    
    // Default for other tokens
    stream.next();
    return null;
  },
  startState() {
    return {};
  }
});

export interface SMTDisplayProps {
  smtCode: string;
  isLoading?: boolean;
  constraintsCount?: number;
}

const SMTDisplay: React.FC<SMTDisplayProps> = ({ 
  smtCode, 
  isLoading = false,
  constraintsCount 
}) => {
  const copyToClipboard = () => {
    navigator.clipboard.writeText(smtCode);
  };

  return (
    <Card className="w-full">
      <CardHeader className="pb-2">
        <div className="flex justify-between items-center">
          <CardTitle className="flex items-center">
            SMT-LIB2 Constraints
          </CardTitle>
          {constraintsCount !== undefined && (
            <Badge variant="outline">
              {constraintsCount} constraints
            </Badge>
          )}
        </div>
      </CardHeader>
      <CardContent>
        {isLoading ? (
          <LoadingState message="Generating SMT constraints..." />
        ) : smtCode ? (
          <div className="space-y-4">
            <div className="flex justify-end">
              <Button 
                variant="outline" 
                size="sm" 
                onClick={copyToClipboard}
                className="flex items-center"
              >
                <Copy className="h-4 w-4 mr-1" />
                Copy to clipboard
              </Button>
            </div>
            <div className="border rounded-md overflow-hidden bg-muted">
              <CodeMirror
                value={smtCode}
                height="400px"
                readOnly={true}
                extensions={[
                  smtLibLanguage,
                  EditorView.lineWrapping
                ]}
                theme="light"
                className="text-sm font-mono"
              />
            </div>
            <p className="text-sm text-muted-foreground">
              These SMT-LIB2 constraints are generated based on the program logic and are used by the Z3 solver to verify the program's correctness.
            </p>
          </div>
        ) : (
          <div className="text-center p-8 text-muted-foreground">
            No SMT constraints generated yet. 
            Run verification to see the constraints.
          </div>
        )}
      </CardContent>
    </Card>
  );
};

export default SMTDisplay;
