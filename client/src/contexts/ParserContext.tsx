import React, { createContext, useContext, useState, ReactNode } from 'react';

interface ASTNode {
  type: string;
  [key: string]: any;
}

interface ParseError {
  message: string;
  line: number;
  column: number;
  expectedToken?: string;
}

interface ParserContextType {
  code: string;
  setCode: (code: string) => void;
  ast: ASTNode | null;
  parseErrors: ParseError[];
  isParsing: boolean;
  parseCode: () => Promise<void>;
}

const defaultContext: ParserContextType = {
  code: '',
  setCode: () => {},
  ast: null,
  parseErrors: [],
  isParsing: false,
  parseCode: async () => {}
};

const ParserContext = createContext<ParserContextType>(defaultContext);

export const useParser = () => useContext(ParserContext);

interface ParserProviderProps {
  children: ReactNode;
  parserService: {
    parse: (code: string) => Promise<{ ast: ASTNode | null; errors: ParseError[] }>;
  };
}

export const ParserProvider: React.FC<ParserProviderProps> = ({ 
  children, 
  parserService 
}) => {
  const [code, setCode] = useState<string>('');
  const [ast, setAST] = useState<ASTNode | null>(null);
  const [parseErrors, setParseErrors] = useState<ParseError[]>([]);
  const [isParsing, setIsParsing] = useState<boolean>(false);

  const parseCode = async () => {
    if (!code.trim()) {
      setAST(null);
      setParseErrors([]);
      return;
    }

    setIsParsing(true);
    try {
      const { ast, errors } = await parserService.parse(code);
      setAST(ast);
      setParseErrors(errors);
    } catch (error) {
      console.error('Error parsing code:', error);
      setAST(null);
      setParseErrors([{
        message: error instanceof Error ? error.message : 'Unknown parsing error',
        line: 1,
        column: 1
      }]);
    } finally {
      setIsParsing(false);
    }
  };

  return (
    <ParserContext.Provider
      value={{
        code,
        setCode,
        ast,
        parseErrors,
        isParsing,
        parseCode
      }}
    >
      {children}
    </ParserContext.Provider>
  );
};
