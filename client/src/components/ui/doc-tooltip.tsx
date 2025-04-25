import React from 'react';
import {
  Tooltip,
  TooltipContent,
  TooltipProvider,
  TooltipTrigger,
} from "./tooltip";
import { HelpCircle } from "lucide-react";

interface DocTooltipProps {
  content: React.ReactNode;
  children?: React.ReactNode;
  className?: string;
  iconSize?: "sm" | "md";
}

export const DocTooltip: React.FC<DocTooltipProps> = ({
  content,
  children,
  className = "",
  iconSize = "sm"
}) => {
  const iconClasses = iconSize === "sm" ? "h-3.5 w-3.5" : "h-4 w-4";
  
  return (
    <TooltipProvider>
      <Tooltip delayDuration={300}>
        <TooltipTrigger asChild>
          <span className={`inline-flex items-center cursor-help text-muted-foreground hover:text-foreground transition-colors ${className}`}>
            {children}
            <HelpCircle className={`ml-1 ${iconClasses}`} />
          </span>
        </TooltipTrigger>
        <TooltipContent className="max-w-[300px] p-3">
          {content}
        </TooltipContent>
      </Tooltip>
    </TooltipProvider>
  );
};
