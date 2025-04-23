# Formal Methods Program Analyzer

A web-based tool that enables users to verify the correctness of programs and check semantic equivalence between different implementations using formal methods.

## Features

- **Program Parsing**: Analyze programs written in a custom mini-language
- **SSA Transformation**: Convert programs to Static Single Assignment form with visualizations
- **Loop Unrolling**: Configure loop unrolling depth for finite analysis
- **SSA Optimizations**: Apply constant propagation, dead code elimination, and common subexpression elimination
- **SMT Generation**: Convert programs to SMT constraints for formal verification
- **Verification**: Check if assertions and postconditions in a program always hold
- **Equivalence Checking**: Determine if two programs are semantically equivalent
- **Control Flow Visualization**: View and interact with control flow graphs
- **Counterexample Generation**: View specific inputs that violate assertions or show inequivalence

## Getting Started

### Prerequisites

- [Node.js](https://nodejs.org/) (v16 or later)
- [pnpm](https://pnpm.io/) (v7 or later)
- [Git](https://git-scm.com/)

### Clone the Repository

```bash
git clone https://github.com/HassanRehman9393/formal-method-project.git
cd formal-method-project
```

### Install Dependencies

```bash
# Install root dependencies
pnpm install

# Install client dependencies
cd client
pnpm install

# Install server dependencies
cd ../server
pnpm install
```

### Running the Client

```bash
# From the project root
cd client
pnpm dev
```

This will start the development server for the client. Open your browser and navigate to `http://localhost:5173` to view the application.

### Running the Server

```bash
# From the project root
cd server
pnpm dev
```

The server will start on port 3000 by default.

### Running Both Client and Server

If you have a script set up in the root package.json, you can run:

```bash
# From the project root
pnpm dev
```

## Project Structure

```
project-root/
├── client/                     # Frontend React application
├── server/                     # Backend Node.js application
├── shared/                     # Shared utilities and types
├── samples/                    # Sample programs
├── tests/                      # Test cases
└── README.md                   # Project documentation
```

## Custom Language Support

The tool supports a custom mini-language with the following features:

- Variable declarations and assignments: `x := 5;`
- Arithmetic and boolean expressions: `x + y * 2`, `x < 5 && y > 0`
- If-else statements: `if (condition) { ... } else { ... }`
- While loops: `while (condition) { ... }`
- For loops: `for (init; condition; update) { ... }`
- Arrays: `arr[i] := value;`
- Assert statements: `assert(condition);`

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## Contributors

- Hassan Rehman
- [Other Team Members]
