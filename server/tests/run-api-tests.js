/**
 * Test runner that starts the server, runs the tests, and then shuts down the server
 */
const { spawn } = require('child_process');
const { runTests } = require('./api-test');

// Configuration
const SERVER_START_TIMEOUT = 5000; // Wait 5 seconds for server to start

/**
 * Start the server as a child process
 * @returns {Object} Child process
 */
function startServer() {
  console.log('Starting server...');
  const server = spawn('node', ['src/index.js'], {
    stdio: 'pipe',
    detached: false
  });
  
  // Log server output
  server.stdout.on('data', (data) => {
    console.log(`Server: ${data.toString().trim()}`);
  });
  
  server.stderr.on('data', (data) => {
    console.error(`Server Error: ${data.toString().trim()}`);
  });
  
  return server;
}

/**
 * Run the API tests
 */
async function run() {
  let server = null;
  
  try {
    // Start the server
    server = startServer();
    
    // Wait for server to start
    console.log(`Waiting ${SERVER_START_TIMEOUT}ms for server to start...`);
    await new Promise(resolve => setTimeout(resolve, SERVER_START_TIMEOUT));
    
    // Run the tests
    await runTests();
  } catch (error) {
    console.error('Error running tests:', error);
  } finally {
    // Clean up server process
    if (server) {
      console.log('Shutting down server...');
      if (process.platform === 'win32') {
        // On Windows we need to use taskkill to kill the process tree
        spawn('taskkill', ['/pid', server.pid, '/f', '/t']);
      } else {
        // On Unix we can use the process group
        process.kill(-server.pid);
      }
    }
  }
}

// Run the tests
run().then(() => {
  process.exit(0);
}).catch(err => {
  console.error('Uncaught error:', err);
  process.exit(1);
});
