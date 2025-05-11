# Formal Methods Program Analyzer - Client

This is the client application for the Formal Methods Program Analyzer, a web-based tool for verifying program correctness and checking semantic equivalence using formal methods.

## Overview

The client application is built with React, Vite, and TypeScript, providing a user-friendly interface for:

- Writing and editing programs in a custom mini-language
- Transforming programs to Static Single Assignment (SSA) form
- Generating SMT constraints for verification
- Verifying program assertions
- Checking semantic equivalence between programs
- Visualizing control flow and verification results

## Getting Started

### Prerequisites

- Node.js 16+ 
- npm or yarn

### Installation

1. Install dependencies:
   ```bash
   npm install
   ```

2. Configure the environment:
   - Copy `.env.example` to `.env`
   - Set `VITE_API_BASE_URL` to point to your server's API (default: http://localhost:3001/api)
   - Set `VITE_USE_MOCK_API` to `false` to use the real backend, or `true` during development if no server is available

3. Start the development server:
   ```bash
   npm run dev
   ```

## API Integration

The client communicates with the server through a set of API endpoints:

- `/parse`: Parses programs into AST
- `/parse/transform-ssa`: Transforms AST to SSA form
- `/verify`: Verifies assertions in a program
- `/verify/generate-smt`: Generates SMT constraints
- `/equivalence`: Checks program equivalence

If the server is not available during development, the client can use mock implementations from:
- `lib/mockSSAService.ts`
- `lib/mockSMTService.ts`

## Project Structure

- `src/components`: React components
- `src/lib`: Core functionality
  - `parser`: Program parsing logic
  - `mockSSAService.ts`: Mock SSA transformation service
  - `mockSMTService.ts`: Mock SMT constraint generation
- `src/contexts`: React context providers
  - `VerificationContext.tsx`: State and logic for verification
- `src/utils`: Utility functions
  - `apiUtils.ts`: API communication utilities

## API Response Format

The API follows a consistent response format:

```typescript
interface ApiResponse<T> {
  success: boolean;
  data?: T;
  message?: string;
}
```

## Common Issues and Fixes

- If you receive a 404 error when trying to access API endpoints, make sure the server is running and the API_BASE_URL is correctly configured.
- If you receive HTML responses instead of JSON, the server might be returning an error page. Check server logs for details.

## Development Mode

In development mode, you can toggle between real API calls and mock implementations by setting the `VITE_USE_MOCK_API` environment variable:

```
# .env
VITE_USE_MOCK_API=true  # Use mock implementations
VITE_USE_MOCK_API=false # Use real API
```

## License

[MIT](LICENSE)
