import { useAppContext } from "@/contexts/AppContext"
import { useEffect } from "react"
import CodeMirror from '@uiw/react-codemirror'
import { javascript } from '@codemirror/lang-javascript'
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card"

const CodeEditor = () => {
  const { mode, program1, setProgram1, program2, setProgram2 } = useAppContext()
  
  // Example initial program
  useEffect(() => {
    if (!program1) {
      setProgram1(
        'x := 0;\nwhile (x < 10) {\n  x := x + 1;\n}\nassert(x == 10);'
      )
    }
  }, [])

  return (
    <div className="space-y-4">
      <Card>
        <CardHeader>
          <CardTitle>Program {mode === 'equivalence' ? '1' : ''}</CardTitle>
        </CardHeader>
        <CardContent>
          <CodeMirror
            value={program1}
            height="200px"
            extensions={[javascript()]}
            onChange={(value) => setProgram1(value)}
          />
        </CardContent>
      </Card>

      {mode === 'equivalence' && (
        <Card>
          <CardHeader>
            <CardTitle>Program 2</CardTitle>
          </CardHeader>
          <CardContent>
            <CodeMirror
              value={program2}
              height="200px"
              extensions={[javascript()]}
              onChange={(value) => setProgram2(value)}
            />
          </CardContent>
        </Card>
      )}
    </div>
  )
}

export default CodeEditor
