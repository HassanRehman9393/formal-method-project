import { useState } from 'react'
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs"
import { Card, CardContent } from "@/components/ui/card"
import { AppProvider } from "@/contexts/AppContext"
import CodeEditor from "@/components/CodeEditor"
import ConfigPanel from "@/components/ConfigPanel"
import ResultView from "@/components/ResultView"
import SSADisplay from "@/components/SSADisplay"
import SMTDisplay from "@/components/SMTDisplay"
import CFGView from "@/components/CFGView"

function App() {
  const [activeTab, setActiveTab] = useState("results")

  return (
    <AppProvider>
      <div className="container mx-auto p-4 min-h-screen">
        <header className="mb-6">
          <h1 className="text-3xl font-bold">Formal Methods Program Analyzer</h1>
          <p className="text-muted-foreground">
            Verify program correctness using formal methods
          </p>
        </header>

        <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
          <div className="lg:col-span-2">
            <ConfigPanel />
            <div className="mt-4">
              <CodeEditor />
            </div>
          </div>

          <div className="lg:col-span-1">
            <Tabs value={activeTab} onValueChange={setActiveTab} className="w-full">
              <TabsList className="w-full grid grid-cols-5">
                <TabsTrigger value="results">Results</TabsTrigger>
                <TabsTrigger value="ssa">SSA</TabsTrigger>
                <TabsTrigger value="opt-ssa">Optimized</TabsTrigger>
                <TabsTrigger value="cfg">CFG</TabsTrigger>
                <TabsTrigger value="smt">SMT</TabsTrigger>
              </TabsList>

              <TabsContent value="results">
                <Card>
                  <CardContent className="pt-6">
                    <ResultView />
                  </CardContent>
                </Card>
              </TabsContent>

              <TabsContent value="ssa">
                <Card>
                  <CardContent className="pt-6">
                    <SSADisplay optimized={false} />
                  </CardContent>
                </Card>
              </TabsContent>

              <TabsContent value="opt-ssa">
                <Card>
                  <CardContent className="pt-6">
                    <SSADisplay optimized={true} />
                  </CardContent>
                </Card>
              </TabsContent>

              <TabsContent value="cfg">
                <Card>
                  <CardContent className="pt-6">
                    <CFGView />
                  </CardContent>
                </Card>
              </TabsContent>

              <TabsContent value="smt">
                <Card>
                  <CardContent className="pt-6">
                    <SMTDisplay />
                  </CardContent>
                </Card>
              </TabsContent>
            </Tabs>
          </div>
        </div>
      </div>
    </AppProvider>
  )
}

export default App
