import { useAppContext } from "@/contexts/AppContext"
import { Button } from "@/components/ui/button"
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue,
} from "@/components/ui/select"
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card"

const ConfigPanel = () => {
  const { 
    mode, 
    setMode, 
    loopUnrollingDepth, 
    setLoopUnrollingDepth,
    setIsLoading,
    // Other state variables will be used later
  } = useAppContext()

  const handleVerify = () => {
    setIsLoading(true)
    // This will be implemented later when we connect with the backend
    setTimeout(() => {
      setIsLoading(false)
    }, 1000)
  }

  return (
    <Card>
      <CardHeader>
        <CardTitle>Configuration</CardTitle>
      </CardHeader>
      <CardContent>
        <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
          <div>
            <label className="block text-sm font-medium mb-1">Mode</label>
            <Select value={mode} onValueChange={(value: any) => setMode(value)}>
              <SelectTrigger>
                <SelectValue placeholder="Select mode" />
              </SelectTrigger>
              <SelectContent>
                <SelectItem value="verification">Verification</SelectItem>
                <SelectItem value="equivalence">Equivalence</SelectItem>
              </SelectContent>
            </Select>
          </div>
          
          <div>
            <label className="block text-sm font-medium mb-1">Loop Unrolling Depth</label>
            <input
              type="number"
              min="1"
              max="10"
              value={loopUnrollingDepth}
              onChange={(e) => setLoopUnrollingDepth(Number(e.target.value))}
              className="w-full px-3 py-2 border rounded-md"
            />
          </div>
          
          <div className="flex items-end">
            <Button onClick={handleVerify} className="w-full">
              {mode === 'verification' ? 'Verify Program' : 'Check Equivalence'}
            </Button>
          </div>
        </div>
      </CardContent>
    </Card>
  )
}

export default ConfigPanel
