# Formal Methods Program Analyzer

## Project Overview

The Formal Methods Program Analyzer is a web-based tool that enables users to verify the correctness of programs and check semantic equivalence between different implementations using formal methods. The tool parses programs written in a custom mini-language, transforms them into SSA (Static Single Assignment) form, generates SMT (Satisfiability Modulo Theories) constraints, and uses the Z3 solver to verify assertions or check program equivalence.

## Key Features

- **Program Parsing**: Analyze programs written in a custom mini-language
- **SSA Transformation**: Convert programs to Static Single Assignment form with visualizations
- **Loop Unrolling**: Configure loop unrolling depth for finite analysis
- **SSA Optimizations**: Apply constant propagation, dead code elimination, and common subexpression elimination
- **SMT Generation**: Convert programs to SMT constraints for formal verification
- **Verification**: Check if assertions and postconditions in a program always hold
- **Equivalence Checking**: Determine if two programs are semantically equivalent
- **Control Flow Visualization**: View and interact with control flow graphs
- **Counterexample Generation**: View specific inputs that violate assertions or show inequivalence

## Core Technology Stack

### Frontend
- **React**: UI framework for building the single-page application
- **Vite**: Build tool and development server
- **Tailwind CSS**: Utility-first CSS framework for styling
- **Shadcn UI**: Component library built on Tailwind CSS
- **CodeMirror**: Code editor with syntax highlighting
- **D3.js**: Library for control flow graph visualization

### Backend
- **Node.js**: JavaScript runtime environment
- **Express**: Web application framework for the API
- **Z3 Solver**: SMT solver for formal verification
- **z3.js**: JavaScript bindings for the Z3 theorem prover

### Core Logic
- **PEG.js**: Parser generator for the custom language
- **Custom SSA Transformer**: For converting code to SSA form
- **Custom SMT Generator**: For generating SMT-LIB format constraints

## Project Structure

```
project-root/
├── client/                     # Frontend React application
│   ├── public/                 # Static assets
│   ├── src/
│   │   ├── components/         # React components
│   │   │   ├── CodeEditor.jsx  # Code input component
│   │   │   ├── ConfigPanel.jsx # Configuration controls
│   │   │   ├── ResultView.jsx  # Results display
│   │   │   ├── SSADisplay.jsx  # SSA visualization
│   │   │   ├── CFGView.jsx     # Control flow graph visualization
│   │   │   └── ...
│   │   ├── lib/                # Core logic modules
│   │   │   ├── parser/         # Language parser
│   │   │   ├── ssa/            # SSA transformation
│   │   │   ├── optimizer/      # SSA optimizations
│   │   │   ├── smtgen/         # SMT constraint generation
│   │   │   └── visualizer/     # Visualization utilities
│   │   ├── contexts/           # React context for state management
│   │   ├── utils/              # Helper functions
│   │   ├── App.jsx             # Main application component
│   │   └── main.jsx            # Entry point
│   ├── package.json            # Frontend dependencies
│   └── vite.config.js          # Vite configuration
│
├── server/                     # Backend Node.js application
│   ├── src/
│   │   ├── routes/             # API routes
│   │   ├── services/           # Backend services
│   │   │   ├── z3Service.js    # Z3 solver integration
│   │   │   └── ...
│   │   └── index.js            # Server entry point
│   └── package.json            # Backend dependencies
│
├── shared/                     # Shared utilities and types
│   └── ...
│
├── samples/                    # Sample programs
├── tests/                      # Test cases
├── README.md                   # Project documentation
└── package.json                # Root package.json for scripts
```

## User Interface

The application consists of a single-page interface with the following main sections:

1. **Mode Selection**: Toggle between verification mode (single program) and equivalence mode (two programs)
2. **Code Input**: CodeMirror editor(s) for entering programs in the custom language
3. **Configuration**: Settings for loop unrolling depth and other parameters
4. **Output Tabs**:
   - **SSA Form**: Display of the program in SSA form
   - **Optimized SSA**: Display of optimized SSA with transformations highlighted
   - **Control Flow Graph**: Interactive visualization of the program's control flow
   - **SMT Constraints**: Generated SMT-LIB format constraints
   - **Results**: Verification results with counterexamples or proof of correctness

## Custom Language Support

The tool supports a custom mini-language with the following features:

- Variable declarations and assignments: `x := 5;`
- Arithmetic and boolean expressions: `x + y * 2`, `x < 5 && y > 0`
- If-else statements: `if (condition) { ... } else { ... }`
- While loops: `while (condition) { ... }`
- For loops: `for (init; condition; update) { ... }`
- Arrays: `arr[i] := value;`
- Assert statements: `assert(condition);`

## Verification Features

The tool performs the following types of verification:

1. **Assertion Checking**: Verifies if all assertions in the program hold for all possible inputs
2. **Program Equivalence**: Checks if two programs produce the same outputs for all possible inputs
3. **Counterexample Generation**: Provides specific inputs that violate assertions or show inequivalence
4. **Proof of Correctness**: Shows examples where programs behave correctly

## Development Team Structure

The project is developed by a three-person team, with each member focusing on specific aspects:

1. **Person 1**: Frontend and UI components
2. **Person 2**: Parser and SSA transformation
3. **Person 3**: SMT generation and solver integration


# Detailed 18-Day Implementation Plan

## Days 1-6: Foundation Phase

### Person 1: UI Setup and Basic Components
1. **Day 1: Project Initialization**
   - Create React project using Vite: `npm create vite@latest fm-analyzer -- --template react`
   - Set up Tailwind CSS: `npm install -D tailwindcss postcss autoprefixer` and initialize
   - Install Shadcn UI: `npx shadcn-ui@latest init`
   - Configure project structure with folders for components, lib, contexts, utils

2. **Day 2: Component Framework**
   - Install CodeMirror: `npm install @uiw/react-codemirror @codemirror/lang-javascript`
   - Create basic layout with Shadcn components:
     - `Card` component for code input areas
     - `Tabs` component for displaying output panels
     - `Button` components for actions
     - `Select` component for mode switching
   - Implement app state management using React Context API

3. **Day 3-4: Code Editor Implementation**
   - Build CodeEditor component with syntax highlighting
   - Implement mode toggle (Verification/Equivalence)
   - Add configuration panel with number input for loop unrolling depth
   - Create placeholder output panels for SSA, SMT, and results

4. **Day 5-6: UI State Management**
   - Implement state management for code input/output
   - Create loading states and error handling components
   - Build the output panel structure with tabs for different views
   - Add placeholder visualizations for later integration

### Person 2: Parser Development
1. **Day 1: Grammar Design**
   - Define tokens for the mini-language (identifiers, operators, keywords)
   - Create formal grammar specification for the language
   - Document language syntax with examples

2. **Day 2: PEG.js Setup**
   - Install PEG.js: `npm install pegjs`
   - Write basic grammar rules in PEG.js format
   - Test simple expressions and assignments

3. **Day 3-4: AST Generation**
   - Define AST node types for all language constructs
   - Implement parser rules for:
     - Variable declarations and assignments
     - Arithmetic and boolean expressions
     - Conditional statements (if-else)
     - Loop constructs (while, for)
     - Array operations
     - Assert statements
   - Add error recovery and reporting

4. **Day 5-6: Parser Integration**
   - Create parser module with clean API
   - Implement test cases for all language features
   - Add support for parsing assertions and post-conditions
   - Create visualization of parse tree for debugging

### Person 3: Backend and Z3 Integration
1. **Day 1: Backend Setup**
   - Initialize Node.js project: `npm init -y`
   - Install Express: `npm install express cors body-parser`
   - Create basic server structure with routes
   - Set up communication between frontend and backend

2. **Day 2: Z3 Research and Setup**
   - Research Z3 integration options (z3.js or child_process)
   - Install z3.js if suitable: `npm install z3-solver`
   - Create basic solver wrapper class
   - Test Z3 with simple constraint problems

3. **Day 3-4: API Design**
   - Design API endpoints:
     - `/verify` for assertion verification
     - `/equivalence` for program equivalence checking
     - `/parse` for AST generation (optional)
   - Implement request/response formats
   - Add error handling and validation

4. **Day 5-6: Basic SMT Generation**
   - Create utility functions for SMT-LIB format generation
   - Implement basic translation for:
     - Variable declarations
     - Arithmetic expressions
     - Boolean expressions
     - Simple assertions
   - Set up test cases for SMT generation

## Days 7-12: Core Functionality Phase

### Person 1: UI Integration
1. **Day 7-8: Parser Output Display**
   - Integrate with Person 2's parser to display parsing results
   - Create visualization for program structure
   - Implement error highlighting in code editor
   - Add ability to edit and re-parse code

2. **Day 9-10: SSA Display**
   - Create component to display SSA form
   - Add side-by-side view of original code and SSA
   - Implement syntax highlighting for SSA code
   - Create toggle for optimized/unoptimized SSA

3. **Day 11-12: SMT Display**
   - Implement component to show SMT constraints
   - Create syntax highlighting for SMT-LIB format
   - Add copy-to-clipboard functionality
   - Connect UI to backend API endpoints

### Person 2: SSA Transformation and Loop Unrolling
1. **Day 7-8: Basic SSA Implementation**
   - Create module for converting AST to SSA form
   - Implement variable renaming and tracking
   - Add support for assignments and expressions
   - Handle conditional statements with phi functions

2. **Day 9-10: Loop Handling**
   - Implement loop detection in AST
   - Create loop unrolling algorithm
   - Support configurable unrolling depth
   - Add handling for nested loops
   - Generate unrolled SSA form

3. **Day 11-12: Basic Optimizations**
   - Implement constant propagation
   - Add control flow graph generation
   - Create data flow analysis framework
   - Implement initial optimization passes

### Person 3: SMT Generation and Verification
1. **Day 7-8: Full SMT Constraint Generation**
   - Extend SMT generation to handle full language
   - Implement array handling in SMT
   - Create translation for control flow constructs
   - Add support for loop invariants

2. **Day 9-10: Verification Logic**
   - Implement assertion checking algorithm
   - Create counterexample extraction
   - Add support for validating postconditions
   - Implement result formatting

3. **Day 11-12: Equivalence Checking**
   - Create algorithm for program equivalence checking
   - Implement input/output comparison
   - Add support for array equivalence
   - Optimize constraint solving

## Days 13-18: Integration and Refinement Phase

### Person 1: UI Finalization
1. **Day 13-14: Results Visualization**
   - Implement counterexample display component
   - Create success case visualization
   - Add detailed explanation of verification results
   - Implement error details display

2. **Day 15-16: Control Flow Visualization**
   - Integrate D3.js for control flow graph
   - Add interactive features (zoom, pan)
   - Create node highlighting for execution paths
   - Add toggle between original and SSA graphs

3. **Day 17-18: Final UI Polish**
   - Add responsive design adjustments
   - Implement keyboard shortcuts
   - Create sample program presets
   - Add documentation and help tooltips
   - Perform cross-browser testing

### Person 2: Advanced SSA and Optimization
1. **Day 13-14: Advanced Optimizations**
   - Implement dead code elimination
   - Add common subexpression elimination
   - Create SSA optimization pipeline
   - Add visualization of optimization effects

2. **Day 15-16: SSA Edge Cases**
   - Handle complex control flow
   - Implement array bounds analysis
   - Add support for complex assertions
   - Optimize SSA generation

3. **Day 17-18: Testing and Refinement**
   - Create comprehensive test suite
   - Fix parser edge cases
   - Optimize SSA transformation
   - Document limitations and assumptions

### Person 3: Solver Optimization and Integration
1. **Day 13-14: Counterexample Generation**
   - Enhance Z3 model extraction
   - Implement multiple counterexample generation
   - Create readable counterexample format
   - Add trace generation for failed assertions

2. **Day 15-16: Performance Optimization**
   - Implement constraint simplification
   - Add timeout handling for solver
   - Create incremental solving approach
   - Optimize array constraint handling

3. **Day 17-18: Final Integration**
   - Complete end-to-end testing
   - Fix edge cases in solver integration
   - Optimize API performance
   - Create documentation for solver limitations

## Integration Tasks for All Team Members

### API Contracts (Day 6)
- Define data formats between:
  - Parser output to SSA conversion
  - SSA output to SMT generation
  - SMT constraints to solver
  - Results from solver to UI

### Integration Testing (Days 10-18)
- Create shared test cases:
  - Simple assignments and conditions
  - Loop examples with different unrolling depths
  - Array manipulations
  - Examples from project description
- Test full workflow daily:
  - Code parsing → SSA conversion → SMT generation → Solving → Results display

### Final Documentation (Days 17-18)
- Document:
  - Language syntax and limitations
  - SSA transformation approach
  - SMT constraint generation strategy
  - Solver capabilities and limitations
  - UI features and usage
- Create user guide with examples
- Prepare sample programs demonstrating all features
