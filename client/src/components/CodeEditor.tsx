import React from "react";
import { Card, CardContent } from "./ui/card";
import CodeMirror from "@uiw/react-codemirror";
import { javascript } from "@codemirror/lang-javascript";
import { Code2, Copy } from "lucide-react";
import { Button } from "./ui/button";
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from "./ui/tooltip";
import { EditorView } from "@codemirror/view";

// Define our light theme styles for CodeMirror
const lightTheme = EditorView.theme({
  "&": {
    backgroundColor: "var(--cm-background, #ffffff)",
    color: "var(--cm-foreground, #1a1a1a)"
  },
  ".cm-content": {
    caretColor: "var(--cm-cursor, #000000)"
  },
  ".cm-cursor, .cm-dropCursor": { 
    borderLeftColor: "var(--cm-cursor, #000000)" 
  },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection": {
    backgroundColor: "rgba(0, 0, 0, 0.1)"
  },
  ".cm-panels": { 
    backgroundColor: "var(--cm-gutter-background, #f5f5f5)", 
    color: "var(--cm-foreground, #1a1a1a)" 
  },
  ".cm-panels.cm-panels-top": { 
    borderBottom: "1px solid rgba(0, 0, 0, 0.1)" 
  },
  ".cm-panels.cm-panels-bottom": { 
    borderTop: "1px solid rgba(0, 0, 0, 0.1)" 
  },
  ".cm-gutters": {
    backgroundColor: "var(--cm-gutter-background, #f5f5f5)",
    color: "var(--cm-gutter-foreground, #6e7781)",
    border: "none"
  },
  ".cm-lineNumbers .cm-gutterElement": {
    padding: "0 16px 0 8px"
  }
});

interface CodeEditorProps {
  value: string;
  onChange: (value: string) => void;
  placeholder?: string;
  title?: string;
  readOnly?: boolean;
}

const CodeEditor: React.FC<CodeEditorProps> = ({
  value,
  onChange,
  placeholder = "Enter your code here...",
  title = "Program",
  readOnly = false,
}) => {
  const copyToClipboard = () => {
    navigator.clipboard.writeText(value);
  };

  return (
    <Card className="w-full border border-border/40 shadow-sm h-full flex flex-col">
      <div className="px-4 py-3 border-b bg-muted/30 flex items-center justify-between">
        <div className="flex items-center space-x-2">
          <Code2 className="h-4 w-4 text-muted-foreground" />
          <h3 className="text-sm font-medium">{title}</h3>
        </div>
        {value && !readOnly && (
          <TooltipProvider>
            <Tooltip>
              <TooltipTrigger asChild>
                <Button 
                  variant="ghost" 
                  size="sm" 
                  onClick={copyToClipboard}
                  className="h-8 w-8 p-0 hover:bg-muted/60 transition-colors"
                >
                  <Copy className="h-3.5 w-3.5" />
                  <span className="sr-only">Copy code</span>
                </Button>
              </TooltipTrigger>
              <TooltipContent side="left">
                <p className="text-xs">Copy to clipboard</p>
              </TooltipContent>
            </Tooltip>
          </TooltipProvider>
        )}
      </div>
      <CardContent className="p-0 overflow-hidden rounded-b-lg flex-grow flex flex-col">
        <CodeMirror
          value={value}
          height="100%"
          extensions={[javascript(), lightTheme]}
          onChange={onChange}
          placeholder={placeholder}
          theme="light"
          readOnly={readOnly}
          className="border-0 flex-grow min-h-[350px]"
          basicSetup={{
            lineNumbers: true,
            foldGutter: true,
            highlightActiveLine: !readOnly,
            highlightSelectionMatches: true,
            syntaxHighlighting: true,
            autocompletion: true,
            closeBrackets: true,
            indentOnInput: true,
          }}
        />
      </CardContent>
    </Card>
  );
};

export default CodeEditor;
