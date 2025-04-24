import React, { useState } from 'react';
import CodeMirror from '@uiw/react-codemirror';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Button } from './ui/button';
import { Tabs, TabsContent, TabsList, TabsTrigger } from './ui/tabs';
import { Clipboard, Check, AlertCircle } from 'lucide-react';
import { Alert, AlertDescription, AlertTitle } from './ui/alert';

// Custom language mode for SMT-LIB syntax highlighting
import { StreamLanguage } from '@codemirror/language';
import { smt2 } from './custom/smt2-lang';

interface SMTDisplayProps {
  smtConstraints: string;
  isLoading: boolean;
  error?: string;
}

const SMTDisplay: React.FC<SMTDisplayProps> = ({
  smtConstraints,
  isLoading,
  error,
}) => {
  const [copied, setCopied] = useState<boolean>(false);
  const [activeTab, setActiveTab] = useState<string>('formatted');

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(smtConstraints);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (err) {
      console.error('Failed to copy text: ', err);
    }
  };

  return (
    <Card className="w-full">
      <CardHeader className="flex flex-row items-center justify-between py-3">
        <CardTitle>SMT Constraints</CardTitle>
        <Button
          variant="outline"
          size="sm"
          onClick={handleCopy}
          disabled={!smtConstraints || isLoading}
        >
          {copied ? (
            <>
              <Check className="mr-2 h-4 w-4" />
              Copied
            </>
          ) : (
            <>
              <Clipboard className="mr-2 h-4 w-4" />
              Copy
            </>
          )}
        </Button>
      </CardHeader>
      <CardContent>
        {isLoading ? (
          <div className="flex justify-center p-4">
            <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-700"></div>
          </div>
        ) : error ? (
          <Alert variant="destructive">
            <AlertCircle className="h-4 w-4" />
            <AlertTitle>Error</AlertTitle>
            <AlertDescription>{error}</AlertDescription>
          </Alert>
        ) : !smtConstraints ? (
          <div className="text-center p-4 text-gray-500">
            No SMT constraints available. Please verify a program first.
          </div>
        ) : (
          <Tabs value={activeTab} onValueChange={setActiveTab}>
            <TabsList>
              <TabsTrigger value="formatted">Formatted</TabsTrigger>
              <TabsTrigger value="raw">Raw</TabsTrigger>
            </TabsList>
            <TabsContent value="formatted" className="mt-2">
              <div className="bg-gray-50 rounded-md overflow-auto">
                <CodeMirror
                  value={smtConstraints}
                  height="300px"
                  extensions={[StreamLanguage.define(smt2)]}
                  editable={false}
                  className="text-sm"
                />
              </div>
            </TabsContent>
            <TabsContent value="raw" className="mt-2">
              <div className="bg-gray-50 rounded-md overflow-auto">
                <pre className="p-4 text-sm font-mono whitespace-pre-wrap">
                  {smtConstraints}
                </pre>
              </div>
            </TabsContent>
          </Tabs>
        )}
      </CardContent>
    </Card>
  );
};

export default SMTDisplay;
