import React from "react";
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";
import { GitGraph, PictureInPicture, Network } from "lucide-react";

interface PlaceholderVisualizationProps {
  type: "ast" | "cfg" | "data-flow";
  title?: string;
}

const PlaceholderVisualization: React.FC<PlaceholderVisualizationProps> = ({ 
  type, 
  title = "Visualization" 
}) => {
  // Choose icon based on visualization type
  const Icon = {
    "ast": PictureInPicture,
    "cfg": GitGraph,
    "data-flow": Network
  }[type];
  
  // Choose description based on visualization type
  const description = {
    "ast": "Abstract Syntax Tree visualization will be available after parsing.",
    "cfg": "Control Flow Graph visualization will be available in future updates.",
    "data-flow": "Data Flow analysis visualization will be implemented soon."
  }[type];
  
  // Choose placeholder grid for visualization
  const PlaceholderContent = () => {
    switch (type) {
      case "ast":
        return (
          <div className="flex justify-center">
            <div className="w-fit p-4">
              <div className="w-12 h-12 rounded-full bg-primary/10 flex items-center justify-center mx-auto mb-2">
                <div className="w-8 h-8 rounded-full bg-primary/20 flex items-center justify-center">
                  <div className="w-4 h-4 rounded-full bg-primary/30"></div>
                </div>
              </div>
              <div className="flex space-x-8 mt-2">
                <div className="flex flex-col items-center">
                  <div className="w-8 h-8 rounded-full bg-primary/10 flex items-center justify-center"></div>
                  <div className="h-6 w-[1px] bg-border"></div>
                  <div className="w-8 h-8 rounded-full bg-primary/10 flex items-center justify-center"></div>
                </div>
                <div className="flex flex-col items-center">
                  <div className="w-8 h-8 rounded-full bg-primary/10 flex items-center justify-center"></div>
                  <div className="h-6 w-[1px] bg-border"></div>
                  <div className="w-8 h-8 rounded-full bg-primary/10 flex items-center justify-center"></div>
                </div>
              </div>
            </div>
          </div>
        );
      case "cfg":
        return (
          <div className="flex justify-center">
            <div className="grid grid-cols-1 gap-3">
              <div className="w-24 h-12 rounded border border-dashed border-primary/50 flex items-center justify-center mx-auto">
                Start
              </div>
              <div className="h-8 w-[1px] bg-border mx-auto"></div>
              <div className="w-24 h-12 rounded border border-dashed border-primary/50 flex items-center justify-center mx-auto">
                If
              </div>
              <div className="flex justify-center">
                <div className="grid grid-cols-2 gap-8">
                  <div className="flex flex-col items-center">
                    <div className="h-8 w-[1px] bg-border"></div>
                    <div className="w-24 h-12 rounded border border-dashed border-primary/50 flex items-center justify-center">
                      Then
                    </div>
                  </div>
                  <div className="flex flex-col items-center">
                    <div className="h-8 w-[1px] bg-border"></div>
                    <div className="w-24 h-12 rounded border border-dashed border-primary/50 flex items-center justify-center">
                      Else
                    </div>
                  </div>
                </div>
              </div>
              <div className="h-8 w-[1px] bg-border mx-auto"></div>
              <div className="w-24 h-12 rounded border border-dashed border-primary/50 flex items-center justify-center mx-auto">
                End
              </div>
            </div>
          </div>
        );
      case "data-flow":
        return (
          <div className="grid grid-cols-3 gap-3 p-4">
            {[...Array(9)].map((_, i) => (
              <div 
                key={i} 
                className="aspect-square rounded border border-dashed border-primary/50 flex items-center justify-center"
              >
                {i % 3 === 0 ? "x_" + Math.floor(i/3) : i % 3 === 1 ? "y_" + Math.floor(i/3) : "z_" + Math.floor(i/3)}
              </div>
            ))}
          </div>
        );
      default:
        return null;
    }
  };

  return (
    <Card>
      <CardHeader className="pb-3">
        <CardTitle className="text-lg font-medium flex items-center">
          <Icon className="mr-2 h-4 w-4 text-muted-foreground" />
          {title}
        </CardTitle>
      </CardHeader>
      <CardContent>
        <div className="flex flex-col items-center justify-center h-[300px] text-center">
          <div className="border border-dashed border-muted-foreground/50 rounded-lg w-full h-full p-6 flex flex-col items-center justify-center">
            <PlaceholderContent />
            <p className="text-sm text-muted-foreground mt-6">{description}</p>
          </div>
        </div>
      </CardContent>
    </Card>
  );
};

export default PlaceholderVisualization;
