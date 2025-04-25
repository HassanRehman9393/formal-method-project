import React from 'react';
import {
  DropdownMenu,
  DropdownMenuContent,
  DropdownMenuItem,
  DropdownMenuLabel,
  DropdownMenuSeparator,
  DropdownMenuTrigger,
} from "./ui/dropdown-menu";
import { Button } from "./ui/button";
import { BookOpen } from "lucide-react";
import { ProgramSample, getSampleByCategory, getEquivalencePrograms } from "../lib/samples";

interface SampleProgramsMenuProps {
  onSelectProgram: (code: string) => void;
  onSelectEquivalencePrograms?: () => void;
  isEquivalenceMode?: boolean;
  programNumber?: 1 | 2;
}

export const SampleProgramsMenu: React.FC<SampleProgramsMenuProps> = ({
  onSelectProgram,
  onSelectEquivalencePrograms,
  isEquivalenceMode = false,
  programNumber
}) => {
  
  const handleSelectSample = (sample: ProgramSample) => {
    onSelectProgram(sample.code);
  };
  
  const handleSelectEquivalence = () => {
    if (onSelectEquivalencePrograms) {
      onSelectEquivalencePrograms();
    }
  };
  
  const basicSamples = getSampleByCategory('basic');
  const loopSamples = getSampleByCategory('loops');
  const arraySamples = getSampleByCategory('arrays');
  
  const menuTitle = programNumber 
    ? `Sample Programs (Program ${programNumber})` 
    : "Sample Programs";
  
  return (
    <DropdownMenu>
      <DropdownMenuTrigger asChild>
        <Button variant="ghost" size="sm" className="flex items-center gap-2">
          <BookOpen className="h-4 w-4" />
          <span className="hidden sm:inline">Examples</span>
        </Button>
      </DropdownMenuTrigger>
      <DropdownMenuContent align="end" className="w-[220px]">
        <DropdownMenuLabel>{menuTitle}</DropdownMenuLabel>
        
        {isEquivalenceMode && onSelectEquivalencePrograms && (
          <>
            <DropdownMenuItem onClick={handleSelectEquivalence} className="cursor-pointer">
              <span className="font-medium">Load equivalence example pair</span>
            </DropdownMenuItem>
            <DropdownMenuSeparator />
          </>
        )}
        
        <DropdownMenuLabel>Basic Examples</DropdownMenuLabel>
        {basicSamples.map((sample) => (
          <DropdownMenuItem 
            key={sample.id}
            onClick={() => handleSelectSample(sample)}
            className="cursor-pointer"
          >
            <div className="flex flex-col">
              <span>{sample.name}</span>
              <span className="text-xs text-muted-foreground">{sample.description}</span>
            </div>
          </DropdownMenuItem>
        ))}
        
        <DropdownMenuSeparator />
        <DropdownMenuLabel>Loops</DropdownMenuLabel>
        {loopSamples.map((sample) => (
          <DropdownMenuItem 
            key={sample.id}
            onClick={() => handleSelectSample(sample)}
            className="cursor-pointer"
          >
            <div className="flex flex-col">
              <span>{sample.name}</span>
              <span className="text-xs text-muted-foreground">{sample.description}</span>
            </div>
          </DropdownMenuItem>
        ))}
        
        <DropdownMenuSeparator />
        <DropdownMenuLabel>Arrays</DropdownMenuLabel>
        {arraySamples.map((sample) => (
          <DropdownMenuItem 
            key={sample.id}
            onClick={() => handleSelectSample(sample)}
            className="cursor-pointer"
          >
            <div className="flex flex-col">
              <span>{sample.name}</span>
              <span className="text-xs text-muted-foreground">{sample.description}</span>
            </div>
          </DropdownMenuItem>
        ))}
      </DropdownMenuContent>
    </DropdownMenu>
  );
};
