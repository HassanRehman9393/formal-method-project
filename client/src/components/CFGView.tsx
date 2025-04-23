import { useAppContext } from "@/contexts/AppContext"

const CFGView = () => {
  const { isLoading } = useAppContext()

  if (isLoading) {
    return <div className="flex justify-center py-8">Loading control flow graph...</div>
  }

  return (
    <div>
      <h3 className="text-lg font-medium mb-4">Control Flow Graph</h3>
      <div className="p-4 border rounded-lg h-[400px] flex items-center justify-center bg-muted">
        <p>Placeholder for control flow graph visualization</p>
        {/* We'll integrate D3.js here later */}
      </div>
    </div>
  )
}

export default CFGView
