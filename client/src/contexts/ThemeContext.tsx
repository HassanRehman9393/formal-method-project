import React, { createContext, useContext, useEffect } from "react";

interface ThemeProviderProps {
  children: React.ReactNode;
}

interface ThemeContextType {
  theme: "light";
}

const initialState: ThemeContextType = {
  theme: "light"
};

const ThemeContext = createContext<ThemeContextType>(initialState);

export function ThemeProvider({
  children,
  ...props
}: ThemeProviderProps) {
  // Always use light theme
  useEffect(() => {
    const root = window.document.documentElement;
    root.classList.remove("dark", "system");
    root.classList.add("light");
    
    // Add CSS variables for CodeMirror light theme
    document.body.style.setProperty('--cm-background', '#ffffff');
    document.body.style.setProperty('--cm-foreground', '#1a1a1a');
    document.body.style.setProperty('--cm-comment', '#6a737d');
    document.body.style.setProperty('--cm-string', '#032f62');
    document.body.style.setProperty('--cm-keyword', '#d73a49');
    document.body.style.setProperty('--cm-variable', '#24292e');
    document.body.style.setProperty('--cm-number', '#005cc5');
    document.body.style.setProperty('--cm-operator', '#d73a49');
    document.body.style.setProperty('--cm-gutter-background', '#f6f8fa');
    document.body.style.setProperty('--cm-gutter-foreground', '#959da5');
    document.body.style.setProperty('--cm-cursor', '#24292e');
  }, []);

  const value: ThemeContextType = {
    theme: "light"
  };

  return (
    <ThemeContext.Provider {...props} value={value}>
      {children}
    </ThemeContext.Provider>
  );
}

export const useTheme = () => {
  const context = useContext(ThemeContext);
  if (context === undefined) {
    throw new Error("useTheme must be used within a ThemeProvider");
  }
  return context;
};
