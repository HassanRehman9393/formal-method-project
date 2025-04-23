import { useAppContext } from "@/contexts/AppContext"

interface SSADisplayProps {
  optimized: boolean
}

const SSADisplay = ({ optimized }: SSADisplayProps) => {
  const { isLoading } = useAppContext()

  if (isLoading) {
    return <div className="flex justify-center py-8">Loading SSA form...</div>
  }

  return (
    <div>
      <h3 className="text-lg font-medium mb-4">
        {optimized ? 'Optimized SSA Form' : 'SSA Form'}
      </h3>
      <div className="p-4 border rounded-lg bg-muted">
        <pre className="whitespace-pre-wrap">
          <code>
            {`// Placeholder for ${optimized ? 'optimized' : ''} SSA form`}
          </code>
        </pre>
      </div>
    </div>
  )
}

export default SSADisplay
