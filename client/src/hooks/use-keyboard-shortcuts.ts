import { useEffect } from 'react';
import { useVerification } from '../contexts/VerificationContext';

export function useKeyboardShortcuts() {
  const {
    runVerification,
    mode,
    setMode,
    setProgram1,
    setProgram2,
    setActiveTab
  } = useVerification();

  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      // Run verification with Ctrl/Cmd + Enter
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        runVerification();
      }

      // Switch to verification mode with Alt + 1
      if (e.altKey && e.key === '1') {
        e.preventDefault();
        setMode('verification');
      }

      // Switch to equivalence mode with Alt + 2
      if (e.altKey && e.key === '2') {
        e.preventDefault();
        setMode('equivalence');
      }

      // Switch tabs with Alt + [Tab Number]
      if (e.altKey) {
        switch (e.key) {
          case 'r':
            e.preventDefault();
            setActiveTab('results');
            break;
          case 's':
            e.preventDefault();
            setActiveTab('ssa');
            break;
          case 'o':
            e.preventDefault();
            setActiveTab('optimized-ssa');
            break;
          case 'm':
            e.preventDefault();
            setActiveTab('smt');
            break;
          case 'c':
            e.preventDefault();
            setActiveTab('cfg');
            break;
        }
      }
    };

    window.addEventListener('keydown', handleKeyDown);

    return () => {
      window.addEventListener('keydown', handleKeyDown);
    };
  }, [runVerification, mode, setMode, setActiveTab, setProgram1, setProgram2]);

  return {
    shortcuts: [
      { key: "Ctrl+Enter", description: "Run verification" },
      { key: "Alt+1", description: "Switch to verification mode" },
      { key: "Alt+2", description: "Switch to equivalence mode" },
      { key: "Alt+R", description: "View results tab" },
      { key: "Alt+S", description: "View SSA tab" },
      { key: "Alt+O", description: "View optimized SSA tab" },
      { key: "Alt+M", description: "View SMT tab" },
      { key: "Alt+C", description: "View CFG tab" },
    ]
  };
}
