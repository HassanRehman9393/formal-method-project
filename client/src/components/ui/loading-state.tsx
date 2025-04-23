import React from "react";
import { Loader2 } from "lucide-react";

interface LoadingStateProps {
  message?: string;
  size?: "sm" | "md" | "lg";
}

export function LoadingState({ message = "Loading...", size = "md" }: LoadingStateProps) {
  const sizeClass = {
    sm: "h-4 w-4",
    md: "h-6 w-6",
    lg: "h-8 w-8",
  }[size];

  return (
    <div className="flex flex-col items-center justify-center space-y-2 p-4">
      <Loader2 className={`animate-spin text-primary ${sizeClass}`} />
      <p className="text-sm text-muted-foreground">{message}</p>
    </div>
  );
}

export function ProcessingSteps({
  isParsingCode,
  isTransformingSsa,
  isGeneratingSmtConstraints,
  isSolving,
}: {
  isParsingCode: boolean;
  isTransformingSsa: boolean;
  isGeneratingSmtConstraints: boolean;
  isSolving: boolean;
}) {
  return (
    <div className="w-full max-w-md mx-auto space-y-2">
      <ProcessingStep 
        completed={!isParsingCode && (isTransformingSsa || isGeneratingSmtConstraints || isSolving)} 
        active={isParsingCode} 
        step={1} 
        title="Parsing Code" 
      />
      <ProcessingStep 
        completed={!isTransformingSsa && (isGeneratingSmtConstraints || isSolving)} 
        active={isTransformingSsa} 
        step={2} 
        title="Transforming to SSA" 
      />
      <ProcessingStep 
        completed={!isGeneratingSmtConstraints && isSolving} 
        active={isGeneratingSmtConstraints} 
        step={3} 
        title="Generating SMT Constraints" 
      />
      <ProcessingStep 
        completed={false} 
        active={isSolving} 
        step={4} 
        title="Solving Constraints" 
      />
    </div>
  );
}

function ProcessingStep({
  completed,
  active,
  step,
  title,
}: {
  completed: boolean;
  active: boolean;
  step: number;
  title: string;
}) {
  return (
    <div className="flex items-center space-x-3">
      <div className={`rounded-full w-6 h-6 flex items-center justify-center text-xs font-medium
        ${completed ? 'bg-primary text-primary-foreground' : 
          active ? 'bg-primary/20 text-primary border border-primary animate-pulse' : 
          'bg-muted text-muted-foreground'}`}>
        {step}
      </div>
      <div className="flex-1">
        <p className={`text-sm font-medium ${active ? 'text-foreground' : 'text-muted-foreground'}`}>
          {title}
        </p>
      </div>
      {active && <Loader2 className="animate-spin h-4 w-4 text-primary" />}
    </div>
  );
}
