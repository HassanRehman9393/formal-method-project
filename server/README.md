# Formal Methods Program Analyzer - Server

This is the server component of the Formal Methods Program Analyzer, providing the backend API for program parsing, verification, and equivalence checking.

## Overview

The server is built with Node.js and Express, providing a REST API for:

- Program parsing and validation
- Static Single Assignment (SSA) transformation
- SMT constraint generation
- Program verification
- Equivalence checking
- Integration with Z3 solver

## Getting Started

### Prerequisites

- Node.js 16+
- npm or yarn
- Z3 solver (optional)

### Installation

1. Install dependencies:
   ```bash
   npm install
   ```

2. Configure environment variables:
   ```bash
   PORT=3001  # API server port
   ```

3. Start the server:
   ```bash
   npm start
   ```

## API Endpoints

### Parser API

- **POST /api/parse**
  - Parses program code into an AST
  - Request: `{ programCode: string }`
  - Response: `{ success: boolean, ast: Object }`

- **POST /api/parse/transform-ssa**
  - Transforms code or AST to SSA form
  - Request: `{ programCode?: string, ast?: Object, loopUnrollingDepth?: number }`
  - Response: `{ success: boolean, ssaAst: Object, ssaCode: string, optimizedSsaCode: string }`

- **POST /api/parse/validate**
  - Validates program syntax
  - Request: `{ programCode: string }`
  - Response: `{ valid: boolean, error?: string }`

### Verification API

- **POST /api/verify**
  - Verifies a program's assertions
  - Request: `{ program: string, options?: Object }`
  - Response: `{ success: boolean, data: { verified: boolean, counterexamples?: Array } }`

- **POST /api/verify/generate-smt**
  - Generates SMT constraints for a program
  - Request: `{ program: string, options?: Object }`
  - Response: `{ success: boolean, data: { smtConstraints: string } }`

### Equivalence API

- **POST /api/equivalence**
  - Checks if two programs are semantically equivalent
  - Request: `{ program1: string, program2: string, options?: Object }`
  - Response: `{ success: boolean, data: { equivalent: boolean, counterexample?: Object } }`

- **POST /api/equivalence/generate-smt**
  - Generates SMT constraints for equivalence checking
  - Request: `{ program: string, secondProgram: string, options?: Object }`
  - Response: `{ success: boolean, data: { smtConstraints: string } }`

### SMT API

- **POST /api/smt/generate**
  - Generates SMT constraints from a program
  - Request: `{ program: string, options?: Object }`
  - Response: `{ success: boolean, data: { smtConstraints: string } }`

- **GET /api/smt/examples**
  - Retrieves example SMT constraints
  - Response: `{ success: boolean, data: { examples: Array } }`

## Project Structure

- `src/controllers/`: API request handlers
- `src/services/`: Core business logic
  - `parserService.js`: Program parsing
  - `ssaService.js`: SSA transformation
  - `smtGenerationService.js`: SMT constraint generation
  - `solverService.js`: Z3 solver integration
  - `verificationService.js`: Program verification
  - `equivalenceService.js`: Equivalence checking
- `src/routes/`: API route definitions
- `src/middleware/`: Express middleware

## API Response Format

All API endpoints follow a consistent response format:

```javascript
{
  success: boolean,  // Whether the operation was successful
  data?: any,        // Response data if successful
  message?: string   // Error message if not successful
}
```

## Development

During development, you can run the server with auto-reload:

```bash
npm run dev
```

The server implements placeholder functionality for parts that would require the Z3 solver in a production environment.

## Testing

You can test basic API functionality using the included test client:

```bash
node test-client.js
```

## License

[MIT](LICENSE) 