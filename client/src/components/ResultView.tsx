import { useAppContext } from "@/contexts/AppContext"

const ResultView = () => {
  const { isLoading, verificationResult } = useAppContext()

  if (isLoading) {
    return <div className="flex justify-center py-8">Loading results...</div>
  }

  if (!verificationResult) {
    return (
      <div className="text-center py-8">
        <p>Run verification to see results</p>
      </div>
    )
  }

  return (
    <div>
      <h3 className="text-lg font-medium mb-4">Verification Results</h3>
      <div className="p-4 border rounded-lg">
        <p>Placeholder for verification results</p>
      </div>
    </div>
  )
}

export default ResultView
