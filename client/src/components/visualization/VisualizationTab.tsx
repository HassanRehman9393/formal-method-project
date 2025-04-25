import React from 'react';
import { Tabs, TabsContent, TabsList, TabsTrigger } from "../ui/tabs";
import CFGContainer from './CFGContainer';
import { Card, CardContent } from "../ui/card";

interface VisualizationTabProps {
  ast: any;
  ssaAst: any;
  executionPaths?: {
    id: string;
    name: string;
    description: string;
    nodes: string[];
  }[];
}

const VisualizationTab: React.FC<VisualizationTabProps> = ({
  ast,
  ssaAst,
  executionPaths = []
}) => {
  return (
    <Card className="w-full">
      <CardContent className="pt-6">
        <Tabs defaultValue="cfg" className="w-full">
          <TabsList>
            <TabsTrigger value="cfg">Control Flow Graph</TabsTrigger>
            {/* Add more visualization tabs in the future */}
          </TabsList>
          
          <TabsContent value="cfg">
            {(ast || ssaAst) ? (
              <CFGContainer
                ast={ast}
                ssaAst={ssaAst}
                paths={executionPaths}
              />
            ) : (
              <div className="flex items-center justify-center h-[300px] text-muted-foreground">
                No program data available for visualization.
              </div>
            )}
          </TabsContent>
        </Tabs>
      </CardContent>
    </Card>
  );
};

export default VisualizationTab;
