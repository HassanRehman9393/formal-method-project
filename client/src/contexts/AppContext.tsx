import { createContext, useContext, useState, ReactNode } from "react"

type VerificationMode = "verification" | "equivalence"

interface AppContextType {
  mode: VerificationMode
  setMode: (mode: VerificationMode) => void
  program1: string
  setProgram1: (code: string) => void
  program2: string
  setProgram2: (code: string) => void
  loopUnrollingDepth: number
  setLoopUnrollingDepth: (depth: number) => void
  isLoading: boolean
  setIsLoading: (loading: boolean) => void
  verificationResult: any | null
  setVerificationResult: (result: any | null) => void
}

const AppContext = createContext<AppContextType | undefined>(undefined)

export function AppProvider({ children }: { children: ReactNode }) {
  const [mode, setMode] = useState<VerificationMode>("verification")
  const [program1, setProgram1] = useState<string>("")
  const [program2, setProgram2] = useState<string>("")
  const [loopUnrollingDepth, setLoopUnrollingDepth] = useState<number>(3)
  const [isLoading, setIsLoading] = useState<boolean>(false)
  const [verificationResult, setVerificationResult] = useState<any | null>(null)

  const value = {
    mode,
    setMode,
    program1,
    setProgram1,
    program2,
    setProgram2,
    loopUnrollingDepth,
    setLoopUnrollingDepth,
    isLoading,
    setIsLoading,
    verificationResult,
    setVerificationResult
  }

  return <AppContext.Provider value={value}>{children}</AppContext.Provider>
}

export function useAppContext() {
  const context = useContext(AppContext)
  if (context === undefined) {
    throw new Error("useAppContext must be used within an AppProvider")
  }
  return context
}
