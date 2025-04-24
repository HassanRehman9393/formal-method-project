import React from 'react';
import { Card, CardContent, CardHeader, CardTitle } from "./ui/card";

interface ASTNode {
  type: string;
  [key: string]: any;
}

interface StructureVisualizerProps {
  ast: ASTNode | null;
}

const ProgramStructureVisualizer: React.FC<StructureVisualizerProps> = ({ ast }) => {
  if (!ast) {
    return (
      <Card className="w-full">
        <CardHeader>
          <CardTitle>Program Structure</CardTitle>
        </CardHeader>
        <CardContent>
          <div className="text-center p-4 text-gray-500">
            No program structure available. Please parse a valid program first.
          </div>
        </CardContent>
      </Card>
    );
  }

  // Function to extract program structure from AST
  const extractProgramStructure = (ast: ASTNode) => {
    const structure: { type: string; label: string; depth: number; }[] = [];
    
    const traverse = (node: ASTNode, depth = 0) => {
      if (!node) return;
      
      // Process node based on type
      switch (node.type) {
        case 'Program':
          structure.push({ type: 'program', label: 'Program', depth });
          if (node.body && Array.isArray(node.body)) {
            node.body.forEach(child => traverse(child, depth + 1));
          }
          break;
          
        case 'VariableDeclaration':
          const varName = node.name || 'unnamed';
          structure.push({ 
            type: 'variable', 
            label: `Variable: ${varName}${node.value ? ` = ${node.value}` : ''}`, 
            depth 
          });
          break;
          
        case 'AssignmentStatement':
          const leftSide = node.left?.name || 'unnamed';
          structure.push({ 
            type: 'assignment', 
            label: `Assignment: ${leftSide}`, 
            depth 
          });
          break;
          
        case 'IfStatement':
          structure.push({ type: 'if', label: 'If Statement', depth });
          if (node.condition) traverse(node.condition, depth + 1);
          if (node.consequent) {
            structure.push({ type: 'then', label: 'Then Block', depth: depth + 1 });
            if (Array.isArray(node.consequent.body)) {
              node.consequent.body.forEach(stmt => traverse(stmt, depth + 2));
            } else {
              traverse(node.consequent, depth + 2);
            }
          }
          if (node.alternate) {
            structure.push({ type: 'else', label: 'Else Block', depth: depth + 1 });
            if (Array.isArray(node.alternate.body)) {
              node.alternate.body.forEach(stmt => traverse(stmt, depth + 2));
            } else {
              traverse(node.alternate, depth + 2);
            }
          }
          break;
          
        case 'WhileLoop':
          structure.push({ type: 'while', label: 'While Loop', depth });
          if (node.condition) traverse(node.condition, depth + 1);
          if (node.body) {
            if (Array.isArray(node.body.body)) {
              node.body.body.forEach(stmt => traverse(stmt, depth + 1));
            } else {
              traverse(node.body, depth + 1);
            }
          }
          break;
          
        case 'ForLoop':
          structure.push({ type: 'for', label: 'For Loop', depth });
          if (node.init) traverse(node.init, depth + 1);
          if (node.condition) traverse(node.condition, depth + 1);
          if (node.update) traverse(node.update, depth + 1);
          if (node.body) {
            if (Array.isArray(node.body.body)) {
              node.body.body.forEach(stmt => traverse(stmt, depth + 1));
            } else {
              traverse(node.body, depth + 1);
            }
          }
          break;
          
        case 'AssertStatement':
          structure.push({ type: 'assert', label: 'Assertion', depth });
          if (node.expression) traverse(node.expression, depth + 1);
          break;
          
        default:
          if (node.type) {
            structure.push({ 
              type: node.type.toLowerCase(), 
              label: `${node.type}${node.operator ? `: ${node.operator}` : ''}`, 
              depth 
            });
          }
          
          // Traverse children based on common patterns
          Object.entries(node).forEach(([key, value]) => {
            if (key === 'type' || key === 'depth' || typeof value !== 'object' || value === null) {
              return;
            }
            
            if (Array.isArray(value)) {
              value.forEach(item => {
                if (item && typeof item === 'object') {
                  traverse(item, depth + 1);
                }
              });
            } else if (typeof value === 'object') {
              traverse(value as ASTNode, depth + 1);
            }
          });
      }
    };
    
    traverse(ast);
    return structure;
  };

  const programStructure = extractProgramStructure(ast);

  return (
    <Card className="w-full">
      <CardHeader>
        <CardTitle>Program Structure</CardTitle>
      </CardHeader>
      <CardContent>
        <div className="bg-gray-50 p-4 rounded-md overflow-auto max-h-[400px]">
          {programStructure.map((item, index) => (
            <div 
              key={index} 
              className="flex items-center py-1"
              style={{ marginLeft: `${item.depth * 20}px` }}
            >
              <div className={`
                w-5 h-5 flex items-center justify-center rounded-full mr-2
                ${getIconColorByType(item.type)}
              `}>
                {getIconByType(item.type)}
              </div>
              <span>{item.label}</span>
            </div>
          ))}
        </div>
      </CardContent>
    </Card>
  );
};

// Helper function to get appropriate icon for structure type
const getIconByType = (type: string) => {
  switch (type) {
    case 'program': return 'P';
    case 'variable': return 'V';
    case 'assignment': return '=';
    case 'if': return 'If';
    case 'then': return 'T';
    case 'else': return 'E';
    case 'while': return 'W';
    case 'for': return 'F';
    case 'assert': return '!';
    case 'binaryexpression': return 'B';
    case 'unaryexpression': return 'U';
    default: return '•';
  }
};

// Helper function to get appropriate color for structure type
const getIconColorByType = (type: string) => {
  switch (type) {
    case 'program': return 'bg-blue-100 text-blue-800';
    case 'variable': return 'bg-green-100 text-green-800';
    case 'assignment': return 'bg-amber-100 text-amber-800';
    case 'if': return 'bg-purple-100 text-purple-800';
    case 'then': case 'else': return 'bg-indigo-100 text-indigo-800';
    case 'while': case 'for': return 'bg-red-100 text-red-800';
    case 'assert': return 'bg-orange-100 text-orange-800';
    case 'binaryexpression': case 'unaryexpression': return 'bg-gray-100 text-gray-800';
    default: return 'bg-gray-100 text-gray-800';
  }
};

export default ProgramStructureVisualizer;
