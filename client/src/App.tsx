import React from "react";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "./components/ui/tabs";
import { Separator } from "./components/ui/separator";
import { Card, CardContent, CardHeader, CardTitle } from "./components/ui/card";
import { VerificationProvider, useVerification } from "./contexts/VerificationContext";
import { FileCode, CheckCircle, Braces, GitGraph, Table, Code2, Settings } from "lucide-react";
import { Alert, AlertDescription } from "./components/ui/alert";

// Import components
import CodeEditor from "./components/CodeEditor";
import ConfigPanel from "./components/ConfigPanel";
import SSADisplay from "./components/SSADisplay";
import SMTDisplay from "./components/SMTDisplay";
import ResultView from "./components/ResultView";
import PlaceholderVisualization from "./components/PlaceholderVisualization";
import { LoadingState, ProcessingSteps } from "./components/ui/loading-state";
import { ErrorDisplay } from "./components/ui/error-display";

const AppContent: React.FC = () => {
  const {
    mode,
    setMode,
    program1,
    setProgram1,
    program2,
    setProgram2,
    loopUnrollingDepth,
    setLoopUnrollingDepth,
    activeTab,
    setActiveTab,
    visualizationType,
    setVisualizationType,
    ssaCode1,
    ssaCode2,
    optimizedSsaCode1,
    optimizedSsaCode2,
    smtConstraints,
    resultStatus,
    resultMessage,
    counterexample,
    executionTime,
    isProcessing,
    isParsingCode,
    isTransformingSsa,
    isGeneratingSmtConstraints,
    isSolving,
    error,
    runVerification,
    clearError,
  } = useVerification();

  return (
    <div className="min-h-screen bg-background flex flex-col">
      <header className="border-b border-border/40 bg-card sticky top-0 z-10 shadow-sm">
        <div className="max-w-7xl mx-auto py-3 px-4 sm:px-6 lg:px-8 flex items-center justify-between">
          <h1 className="text-lg font-bold flex items-center">
            <FileCode className="mr-2 h-5 w-5 text-primary" />
            <span>Formal Methods Program Analyzer</span>
          </h1>
        </div>
      </header>

      <main className="flex-1 max-w-7xl w-full mx-auto py-6 px-4 sm:px-6 lg:px-8 flex flex-col">
        {/* Error Display */}
        {error && (
          <div className="mb-6">
            <ErrorDisplay 
              error={error} 
              onDismiss={clearError}
              onRetry={isProcessing ? undefined : runVerification} 
            />
          </div>
        )}
        
        {/* Processing Status Display */}
        {isProcessing && (
          <div className="mb-6">
            <Card>
              <CardHeader className="pb-3">
                <CardTitle className="text-lg font-medium">Processing</CardTitle>
              </CardHeader>
              <CardContent>
                <ProcessingSteps 
                  isParsingCode={isParsingCode}
                  isTransformingSsa={isTransformingSsa}
                  isGeneratingSmtConstraints={isGeneratingSmtConstraints}
                  isSolving={isSolving}
                />
              </CardContent>
            </Card>
          </div>
        )}

        {/* Main Layout - Two Column */}
        <div className="grid grid-cols-1 lg:grid-cols-4 gap-6 mb-8">
          {/* Configuration Panel - Fixed Width */}
          <div className="lg:col-span-1">
            <div className="mb-3 flex items-center space-x-2 text-base font-medium">
              <Settings className="h-4 w-4 text-muted-foreground" />
              <h2>Analysis Settings</h2>
            </div>
            <ConfigPanel
              mode={mode}
              onModeChange={setMode}
              loopUnrollingDepth={loopUnrollingDepth}
              onLoopUnrollingDepthChange={setLoopUnrollingDepth}
              onVerify={runVerification}
              isProcessing={isProcessing}
            />
          </div>
          
          {/* Code Editor Area - Flexible Width */}
          <div className="lg:col-span-3">
            <div className="mb-3 flex items-center space-x-2 text-base font-medium">
              <Code2 className="h-4 w-4 text-muted-foreground" />
              <h2>Source Code</h2>
            </div>
            <div className={`grid ${mode === 'equivalence' ? 'grid-cols-1 md:grid-cols-2 gap-6' : 'grid-cols-1'}`}>
              <CodeEditor
                value={program1}
                onChange={setProgram1}
                title={mode === 'equivalence' ? "Program 1" : "Program"}
                placeholder={`// Enter your program here...\n// Example:\n\nx := 0;\ni := 0;\nwhile (i < 10) {\n  i := i + 1;\n  x := x + i;\n}\nassert(x >= 0);`}
              />
              
              {mode === 'equivalence' && (
                <CodeEditor
                  value={program2}
                  onChange={setProgram2}
                  title="Program 2"
                  placeholder={`// Enter your second program here...\n// Example:\n\nx := 0;\nsum := 0;\nfor (i := 1; i <= 10; i := i + 1) {\n  sum := sum + i;\n}\nx := sum;\nassert(x >= 0);`}
                />
              )}
            </div>
          </div>
        </div>
        
        <Separator className="my-6" />
        
        {/* Results Area with Tabs */}
        <div className="mb-6">
          <div className="mb-4">
            <h2 className="text-lg font-medium flex items-center">
              <CheckCircle className="mr-2 h-4 w-4 text-muted-foreground" />
              Analysis Results
            </h2>
          </div>
          
          <Tabs 
            value={activeTab} 
            onValueChange={(value) => setActiveTab(value as any)} 
            className="w-full"
          >
            <div className="mb-4 overflow-x-auto scrollbar-hide">
              <TabsList className="inline-flex min-w-max w-auto p-1">
                <TabsTrigger value="results" className="flex items-center px-4">
                  <CheckCircle className="mr-2 h-4 w-4" />
                  <span>Results</span>
                </TabsTrigger>
                <TabsTrigger value="ssa" className="flex items-center px-4">
                  <Table className="mr-2 h-4 w-4" />
                  <span>SSA Form</span>
                </TabsTrigger>
                <TabsTrigger value="optimized-ssa" className="flex items-center px-4">
                  <Table className="mr-2 h-4 w-4" />
                  <span>Optimized SSA</span>
                </TabsTrigger>
                <TabsTrigger value="smt" className="flex items-center px-4">
                  <Braces className="mr-2 h-4 w-4" />
                  <span>SMT</span>
                </TabsTrigger>
                <TabsTrigger value="cfg" className="flex items-center px-4">
                  <GitGraph className="mr-2 h-4 w-4" />
                  <span>CFG</span>
                </TabsTrigger>
              </TabsList>
            </div>
            
            <div className="border rounded-lg overflow-hidden bg-card">
              <TabsContent value="results" className="m-0 p-4">
                {isProcessing ? (
                  <LoadingState message="Processing your verification request..." />
                ) : (
                  <ResultView
                    status={resultStatus}
                    message={resultMessage}
                    counterexample={counterexample || undefined}
                    executionTime={executionTime || 0}
                  />
                )}
              </TabsContent>
              
              <TabsContent value="ssa" className="m-0 p-4">
                <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
                  <SSADisplay
                    ssaCode={ssaCode1}
                    isLoading={isProcessing && (isParsingCode || isTransformingSsa)}
                    title={mode === 'equivalence' ? "SSA Form - Program 1" : "SSA Form"}
                  />
                  {mode === 'equivalence' && (
                    <SSADisplay
                      ssaCode={ssaCode2}
                      isLoading={isProcessing && (isParsingCode || isTransformingSsa)}
                      title="SSA Form - Program 2"
                    />
                  )}
                </div>
              </TabsContent>
              
              <TabsContent value="optimized-ssa" className="m-0 p-4">
                <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
                  <SSADisplay
                    ssaCode={optimizedSsaCode1}
                    isLoading={isProcessing && (isParsingCode || isTransformingSsa)}
                    title={mode === 'equivalence' ? "Optimized SSA - Program 1" : "Optimized SSA"}
                    optimized={true}
                  />
                  {mode === 'equivalence' && (
                    <SSADisplay
                      ssaCode={optimizedSsaCode2}
                      isLoading={isProcessing && (isParsingCode || isTransformingSsa)}
                      title="Optimized SSA - Program 2"
                      optimized={true}
                    />
                  )}
                </div>
              </TabsContent>
              
              <TabsContent value="smt" className="m-0 p-4">
                <SMTDisplay
                  smtCode={smtConstraints}
                  isLoading={isProcessing && (isParsingCode || isTransformingSsa || isGeneratingSmtConstraints)}
                  constraintsCount={smtConstraints ? (smtConstraints.match(/\(assert/g) || []).length : undefined}
                />
              </TabsContent>
              
              <TabsContent value="cfg" className="m-0 p-4">
                <PlaceholderVisualization type="cfg" title="Control Flow Graph" />
              </TabsContent>
            </div>
          </Tabs>
        </div>
        
        {/* Additional Visualizations (Placeholder) */}
        <div className="mb-6">
          <div className="mb-4">
            <h2 className="text-lg font-medium">Visualizations</h2>
          </div>
          <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
            <PlaceholderVisualization type="ast" title="Abstract Syntax Tree" />
            <PlaceholderVisualization type="data-flow" title="Data Flow Analysis" />
          </div>
        </div>
      </main>

      <footer className="border-t border-border/40 py-3 bg-card mt-auto">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="flex flex-col md:flex-row justify-between items-center">
            <p className="text-xs text-muted-foreground">
              Formal Methods Program Analyzer © 2023
            </p>
            <div className="flex space-x-6 mt-2 md:mt-0">
              <p className="text-xs text-muted-foreground">
                Built with React + ShadcnUI
              </p>
            </div>
          </div>
        </div>
      </footer>
    </div>
  );
};

const App: React.FC = () => {
  return (
    <VerificationProvider>
      <AppContent />
    </VerificationProvider>
  );
};

export default App;