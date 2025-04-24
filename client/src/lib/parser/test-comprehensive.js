/**
 * Comprehensive test script for the mini-language parser
 * This tests all language features, including the new post-condition support
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { parseProgram, ParseError } from './index.js';
import { generateDotGraph, generateTreeHTML } from './visualizer.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const outputDir = path.join(__dirname, '../../../tests/parser-output');

// Ensure output directory exists
try {
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }
} catch (err) {
  console.error('Failed to create output directory:', err);
}

// Helper function to save visualization output
function saveVisualization(filename, ast, index) {
  try {
    // Save DOT file
    const dotContent = generateDotGraph(ast);
    fs.writeFileSync(path.join(outputDir, `${filename}-${index}.dot`), dotContent);
    
    // Save HTML visualization
    const htmlContent = generateTreeHTML(ast);
    fs.writeFileSync(path.join(outputDir, `${filename}-${index}.html`), htmlContent);
    
    // Save AST as JSON
    fs.writeFileSync(
      path.join(outputDir, `${filename}-${index}.json`), 
      JSON.stringify(ast, null, 2)
    );
    
    console.log(`Visualization saved for ${filename}-${index}`);
  } catch (err) {
    console.error('Failed to save visualization:', err);
  }
}

// Comprehensive test cases covering all language features
const testCases = [
  // 1. Basic Assignments
  {
    category: 'assignments',
    cases: [
      { name: 'simple', code: 'x := 5;' },
      { name: 'chained', code: 'x := y := z := 10;' },
      { name: 'arithmetic', code: 'result := 2 + 3 * 4;' },
      { name: 'boolean', code: 'flag := true && false || true;' },
      { name: 'relational', code: 'check := x > 0 && y <= 10;' },
    ]
  },
  
  // 2. Array Operations
  {
    category: 'arrays',
    cases: [
      { name: 'array-assignment', code: 'arr[0] := 42;' },
      { name: 'array-complex-index', code: 'arr[i+1] := arr[i] * 2;' },
      { name: 'array-access', code: 'x := arr[i];' },
      { name: 'nested-array', code: 'matrix[i][j] := i*j;' }
    ]
  },
  
  // 3. Control Flow - If statements
  {
    category: 'if-statements',
    cases: [
      { name: 'if-simple', code: 'if (x > 0) { y := 1; }' },
      { name: 'if-else', code: 'if (x > 0) { y := 1; } else { y := -1; }' },
      { name: 'if-nested', code: 'if (x > 0) { if (y > 0) { z := 1; } else { z := 2; } } else { z := 3; }' }
    ]
  },
  
  // 4. Control Flow - Loops
  {
    category: 'loops',
    cases: [
      { name: 'while-simple', code: 'while (i < 10) { i := i + 1; }' },
      { name: 'for-simple', code: 'for (i := 0; i < 10; i := i + 1) { sum := sum + i; }' },
      { name: 'for-empty-parts', code: 'for (;;) { x := x + 1; }' },
      { name: 'nested-loops', code: 'for (i := 0; i < n; i := i + 1) { for (j := 0; j < m; j := j + 1) { sum := sum + 1; } }' }
    ]
  },
  
  // 5. Verification Statements
  {
    category: 'verification',
    cases: [
      { name: 'assert-simple', code: 'assert(x > 0);' },
      { name: 'postcondition', code: 'postcondition(y == x * 2);' },
      { name: 'multiple', code: 'assert(x > 0); postcondition(y == x * 2);' }
    ]
  },
  
  // 6. Complex Programs
  {
    category: 'complex',
    cases: [
      { 
        name: 'sum-array', 
        code: `
          sum := 0;
          for (i := 0; i < n; i := i + 1) {
            sum := sum + arr[i];
          }
          postcondition(sum >= 0);
        `
      },
      { 
        name: 'factorial', 
        code: `
          factorial := 1;
          for (i := 1; i <= n; i := i + 1) {
            factorial := factorial * i;
          }
          assert(factorial > 0);
          postcondition(n < 0 || factorial >= n);
        `
      },
      { 
        name: 'binary-search', 
        code: `
          // Binary search in a sorted array
          left := 0;
          right := length - 1;
          found := false;
          
          while (left <= right && !found) {
            mid := (left + right) / 2;
            
            if (arr[mid] == target) {
              found := true;
            } else if (arr[mid] < target) {
              left := mid + 1;
            } else {
              right := mid - 1;
            }
          }
          
          postcondition(!found || arr[mid] == target);
        `
      }
    ]
  }
];

// Run tests
console.log('Running comprehensive parser tests...\n');

let passCount = 0;
let failCount = 0;
let totalTests = 0;

// Count total tests
testCases.forEach(category => {
  totalTests += category.cases.length;
});

for (const category of testCases) {
  console.log(`\n=== Testing ${category.category.toUpperCase()} ===\n`);
  
  for (const [index, test] of category.cases.entries()) {
    console.log(`Test: ${test.name}`);
    console.log(`Code: ${test.code.trim().split('\n').join('\n      ')}`);
    
    try {
      const ast = parseProgram(test.code);
      console.log('✅ PASS\n');
      passCount++;
      
      // Generate and save visualizations
      saveVisualization(`${category.category}-${test.name}`, ast, index);
    } catch (error) {
      console.log('❌ FAIL:', error instanceof ParseError ? error.getFormattedMessage() : error.message);
      failCount++;
    }
  }
}

// Summary
console.log('\n=== Test Summary ===');
console.log(`Total: ${totalTests}`);
console.log(`Passed: ${passCount}`);
console.log(`Failed: ${failCount}`);

if (failCount === 0) {
  console.log('\n🎉 All tests passed!');
} else {
  console.log('\n❌ Some tests failed.');
}

// Generate a test report
const reportContent = `
# Parser Test Report

Generated: ${new Date().toISOString()}

## Summary
- Total tests: ${totalTests}
- Passed: ${passCount}
- Failed: ${failCount}

## Details

${testCases.map(category => `
### ${category.category.toUpperCase()}

${category.cases.map((test, i) => `
#### ${test.name}
\`\`\`
${test.code.trim()}
\`\`\`

- Status: ${failCount === 0 ? '✅ PASS' : '❌ FAIL'}
- Visualization: [View Tree](${category.category}-${test.name}-${i}.html)
`).join('')}
`).join('')}

## Generated Files
${testCases.flatMap((category, i) => 
  category.cases.map((test, j) => `
- ${category.category}-${test.name}-${j}.dot
- ${category.category}-${test.name}-${j}.html
- ${category.category}-${test.name}-${j}.json
`)
).join('')}
`;

fs.writeFileSync(path.join(outputDir, 'test-report.md'), reportContent);
console.log(`\nTest report saved to ${path.join(outputDir, 'test-report.md')}`);
