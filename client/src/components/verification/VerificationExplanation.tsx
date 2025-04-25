import React from 'react';
import { Card, CardContent } from "../ui/card";
import { Accordion, AccordionContent, AccordionItem, AccordionTrigger } from "../ui/accordion";
import { HelpCircle } from "lucide-react";

interface VerificationExplanationProps {
  result: {
    success: boolean;
    message: string;
    details?: {
      explanation: string;
      technicalDetails?: string;
      suggestedFixes?: string[];
    };
  };
}

const VerificationExplanation: React.FC<VerificationExplanationProps> = ({ result }) => {
  if (!result || !result.details) return null;
  
  const { details } = result;

  return (
    <Card className="mb-4">
      <CardContent className="pt-4">
        <div className="flex items-center gap-2 mb-2">
          <HelpCircle className="h-4 w-4 text-muted-foreground" />
          <h3 className="text-md font-medium">Verification Explanation</h3>
        </div>
        
        <p className="text-sm mb-3">{details.explanation}</p>
        
        <Accordion type="single" collapsible className="w-full">
          {details.technicalDetails && (
            <AccordionItem value="technical-details">
              <AccordionTrigger className="text-sm font-medium">
                Technical Details
              </AccordionTrigger>
              <AccordionContent>
                <div className="bg-muted p-3 rounded-md">
                  <pre className="text-xs whitespace-pre-wrap">{details.technicalDetails}</pre>
                </div>
              </AccordionContent>
            </AccordionItem>
          )}
          
          {details.suggestedFixes && details.suggestedFixes.length > 0 && (
            <AccordionItem value="suggested-fixes">
              <AccordionTrigger className="text-sm font-medium">
                Suggested Fixes
              </AccordionTrigger>
              <AccordionContent>
                <ul className="list-disc pl-5 space-y-1">
                  {details.suggestedFixes.map((fix, idx) => (
                    <li key={idx} className="text-sm">{fix}</li>
                  ))}
                </ul>
              </AccordionContent>
            </AccordionItem>
          )}
        </Accordion>
      </CardContent>
    </Card>
  );
};

export default VerificationExplanation;
