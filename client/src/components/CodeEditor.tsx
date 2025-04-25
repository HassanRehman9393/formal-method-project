import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import CodeMirror from '@uiw/react-codemirror';
import { javascript } from '@codemirror/lang-javascript';
import { Play, RefreshCw, Info } from 'lucide-react';
import { Button } from './ui/button';
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from './ui/tooltip';
import { EditorView, Decoration } from '@codemirror/view';
import { Badge } from './ui/badge';

interface ParseError {
  message: string;
  line: number;
  column: number;
  expectedToken?: string;
}

interface CodeEditorProps {
  title: string;
  value: string;
  onChange: (code: string) => void;
  placeholder?: string;
  onParse?: () => void;
  parseErrors?: ParseError[];
  isProcessing?: boolean;
}

const CodeEditor: React.FC<CodeEditorProps> = ({
  title,
  value,
  onChange,
  placeholder = "",
  onParse,
  parseErrors = [],
  isProcessing = false,
}) => {
  // Custom extension for error highlighting
  const errorHighlighting = React.useMemo(() => {
    return [
      javascript({ jsx: false }),
      EditorView.decorations.of((view) => {
        if (!parseErrors.length) return Decoration.none;
        
        const decorations = parseErrors.flatMap(error => {
          const line = error.line - 1;
          if (line < 0 || line >= view.state.doc.lines) return [];
          
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
    <Card className="w-full h-full flex flex-col">
      <CardHeader className="flex flex-row items-center justify-between py-3">
        <div className="flex items-center">
          <CardTitle className="text-xl font-bold">{title}</CardTitle>
          {parseErrors.length > 0 && (
            <Badge variant="destructive" className="ml-2">
              {parseErrors.length} error{parseErrors.length > 1 ? 's' : ''}
            </Badge>
          )}
        </div>
        <div className="flex space-x-2">
          <TooltipProvider>
            <Tooltip>
              <TooltipTrigger asChild>
                <Button 
                  onClick={() => onChange('')} 
                  variant="outline" 
                  size="sm"
                  className="h-8 w-8 p-0"
                >
                  <RefreshCw className="h-4 w-4" />
                </Button>
              </TooltipTrigger>
              <TooltipContent>
                <p>Clear code</p>
              </TooltipContent>
            </Tooltip>
          </TooltipProvider>
          
          {onParse && (
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
                  <p>Parse code (Ctrl+Enter)</p>
                </TooltipContent>
              </Tooltip>
            </TooltipProvider>
          )}
        </div>
      </CardHeader>
      
      <CardContent className="flex-1 pb-6">
        <div className="relative h-full flex flex-col">
          <CodeMirror
            value={value}
            height="100%"
            minHeight="300px"
            extensions={[errorHighlighting, EditorView.lineWrapping]}
            onChange={onChange}
            className="border rounded flex-1"
            theme="light"
            placeholder={placeholder}
          />
          
          {parseErrors.length > 0 && (
            <TooltipProvider>
              <Tooltip>
                <TooltipTrigger asChild>
                  <div className="absolute bottom-2 right-2 bg-red-100 text-red-800 text-xs px-2 py-1 rounded flex items-center cursor-help">
                    <Info className="h-3 w-3 mr-1" />
                    {parseErrors.length} error{parseErrors.length > 1 ? 's' : ''}
                  </div>
                </TooltipTrigger>
                <TooltipContent>
                  <div className="max-h-[200px] overflow-y-auto">
                    <p className="font-semibold mb-1">Parse Errors:</p>
                    <ul className="list-disc pl-4">
                      {parseErrors.slice(0, 5).map((error, idx) => (
                        <li key={idx} className="text-xs">
                          Line {error.line}, Col {error.column}: {error.message}
                        </li>
                      ))}
                      {parseErrors.length > 5 && (
                        <li className="text-xs font-italic">
                          ...and {parseErrors.length - 5} more errors
                        </li>
                      )}
                    </ul>
                  </div>
                </TooltipContent>
              </Tooltip>
            </TooltipProvider>
          )}
        </div>
      </CardContent>
    </Card>
  );
};

export default CodeEditor;
