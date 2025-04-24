import React, { useEffect } from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import CodeMirror from '@uiw/react-codemirror';
import { javascript } from '@codemirror/lang-javascript';
import { Play, RefreshCw } from 'lucide-react';
import { Button } from './ui/button';
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from './ui/tooltip';
import { EditorView, Decoration } from '@codemirror/view';

interface ParseError {
  message: string;
  line: number;
  column: number;
  expectedToken?: string;
}

interface CodeEditorProps {
  title: string;
  code: string;
  onChange: (code: string) => void;
  onParse: () => void;
  parseErrors?: ParseError[];
  isProcessing?: boolean;
}

const CodeEditor: React.FC<CodeEditorProps> = ({
  title,
  code,
  onChange,
  onParse,
  parseErrors = [],
  isProcessing = false,
}) => {
  // Create error markers for CodeMirror
  const errorMarkers = parseErrors.map(error => ({
    from: { line: error.line - 1, ch: error.column - 1 },
    to: { line: error.line - 1, ch: error.column + 1 },
    message: error.message,
    severity: 'error',
  }));

  // Custom extension for error highlighting
  const errorHighlighting = React.useMemo(() => {
    return [
      javascript({ jsx: false }),
      EditorView.decorations.of((view) => {
        if (!parseErrors.length) return Decoration.none;
        
        const decorations = parseErrors.flatMap(error => {
          const line = error.line - 1;
          const lineText = view.state.doc.line(line + 1).text;
          
          const startPos = view.state.doc.line(line + 1).from + Math.max(0, error.column - 1);
          const endPos = Math.min(
            view.state.doc.line(line + 1).to,
            startPos + (error.expectedToken?.length || 1)
          );
          
          return [
            Decoration.mark({
              class: 'cm-error-underline',
              attributes: { title: error.message }
            }).range(startPos, endPos),
            Decoration.line({
              class: 'cm-error-line',
              attributes: { title: error.message }
            }).range(view.state.doc.line(line + 1).from, view.state.doc.line(line + 1).from)
          ];
        });
        
        return Decoration.set(decorations);
      })
    ];
  }, [parseErrors]);

  return (
    <Card className="w-full">
      <CardHeader className="flex flex-row items-center justify-between py-3">
        <CardTitle className="text-xl font-bold">{title}</CardTitle>
        <div className="flex space-x-2">
          <TooltipProvider>
            <Tooltip>
              <TooltipTrigger asChild>
                <Button 
                  onClick={() => onChange('')} 
                  variant="outline" 
                  size="sm"
                >
                  <RefreshCw className="h-4 w-4" />
                </Button>
              </TooltipTrigger>
              <TooltipContent>
                <p>Clear</p>
              </TooltipContent>
            </Tooltip>
          </TooltipProvider>
          <TooltipProvider>
            <Tooltip>
              <TooltipTrigger asChild>
                <Button 
                  onClick={onParse} 
                  variant="default" 
                  size="sm"
                  disabled={isProcessing}
                >
                  {isProcessing ? (
                    <div className="flex items-center space-x-1">
                      <div className="animate-spin rounded-full h-3 w-3 border-b-2 border-white"></div>
                      <span>Parsing...</span>
                    </div>
                  ) : (
                    <>
                      <Play className="h-4 w-4 mr-1" />
                      Parse
                    </>
                  )}
                </Button>
              </TooltipTrigger>
              <TooltipContent>
                <p>Parse code</p>
              </TooltipContent>
            </Tooltip>
          </TooltipProvider>
        </div>
      </CardHeader>
      <CardContent>
        <div className="relative">
          <CodeMirror
            value={code}
            height="300px"
            extensions={[javascript(), EditorView.lineWrapping]}
            onChange={onChange}
            className="border rounded"
            theme="light"
          />
          {parseErrors.length > 0 && (
            <div className="absolute bottom-2 right-2 bg-red-100 text-red-800 text-xs px-2 py-1 rounded">
              {parseErrors.length} error{parseErrors.length > 1 ? 's' : ''}
            </div>
          )}
        </div>
      </CardContent>
    </Card>
  );
};

export default CodeEditor;
