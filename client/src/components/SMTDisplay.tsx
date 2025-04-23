import { useAppContext } from "@/contexts/AppContext"

const SMTDisplay = () => {
  const { isLoading } = useAppContext()

  if (isLoading) {
    return <div className="flex justify-center py-8">Loading SMT constraints...</div>
  }

  return (
    <div>
      <h3 className="text-lg font-medium mb-4">SMT Constraints</h3>
      <div className="p-4 border rounded-lg bg-muted">
        <pre className="whitespace-pre-wrap">
          <code>
            {`// Placeholder for SMT constraints`}
          </code>
        </pre>
      </div>
    </div>
  )
}

export default SMTDisplay
