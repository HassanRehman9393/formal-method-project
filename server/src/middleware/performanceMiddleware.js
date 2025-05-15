/**
 * Performance Middleware
 * Provides performance optimization for API endpoints
 */
const z3Service = require('../services/z3Service');

/**
 * Cache for API responses
 */
const responseCache = new Map();

/**
 * Maximum number of cached responses
 */
const MAX_CACHE_SIZE = 100;

/**
 * Cache TTL in milliseconds (10 minutes)
 */
const CACHE_TTL = 10 * 60 * 1000;

/**
 * Request rate limiting configuration
 */
const rateLimits = {
  verify: { windowMs: 60000, maxRequests: 20 },
  equivalence: { windowMs: 60000, maxRequests: 10 },
  optimize: { windowMs: 60000, maxRequests: 30 }
};

/**
 * Rate limiting data store
 */
const rateLimitStore = new Map();

/**
 * Clean expired rate limit entries
 */
function cleanRateLimitStore() {
  const now = Date.now();
  for (const [ip, endpoints] of rateLimitStore.entries()) {
    for (const [endpoint, data] of Object.entries(endpoints)) {
      if (now - data.windowStart > rateLimits[endpoint].windowMs) {
        // Reset the window if it has expired
        endpoints[endpoint] = {
          windowStart: now,
          count: 0
        };
      }
    }
    
    // Remove empty IPs
    if (Object.keys(endpoints).length === 0) {
      rateLimitStore.delete(ip);
    }
  }
}

// Clean rate limit store every minute
setInterval(cleanRateLimitStore, 60000);

/**
 * Clean expired cache entries
 */
function cleanCache() {
  const now = Date.now();
  for (const [key, entry] of responseCache.entries()) {
    if (now - entry.timestamp > CACHE_TTL) {
      responseCache.delete(key);
    }
  }
  
  // If we're still over the limit, remove oldest entries
  if (responseCache.size > MAX_CACHE_SIZE) {
    const entries = Array.from(responseCache.entries())
      .sort((a, b) => a[1].timestamp - b[1].timestamp);
    
    const toRemove = entries.slice(0, entries.length - MAX_CACHE_SIZE);
    for (const [key] of toRemove) {
      responseCache.delete(key);
    }
  }
}

// Clean cache every 5 minutes
setInterval(cleanCache, 5 * 60 * 1000);

/**
 * Create a cache key from request data
 * @param {Object} req - Express request object
 * @returns {string} Cache key
 */
function createCacheKey(req) {
  const endpoint = req.originalUrl;
  const method = req.method;
  
  // Extract key data from request body
  let bodyKey = '';
  if (req.body) {
    try {
      // For verification requests, cache based on the program and options
      if (req.body.program) {
        bodyKey = `program:${hashString(req.body.program)}`;
      } else if (req.body.ast) {
        bodyKey = `ast:${hashString(JSON.stringify(req.body.ast))}`;
      }
      
      // Add options hash
      if (req.body.options) {
        bodyKey += `-options:${hashString(JSON.stringify(req.body.options))}`;
      }
    } catch (error) {
      // Fallback if we can't process the body
      bodyKey = `body:${hashString(JSON.stringify(req.body))}`;
    }
  }
  
  return `${method}-${endpoint}-${bodyKey}`;
}

/**
 * Simple string hashing function
 * @param {string} str - String to hash
 * @returns {string} Hash
 */
function hashString(str) {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash; // Convert to 32bit integer
  }
  return hash.toString(16);
}

/**
 * Response caching middleware
 * @param {Object} req - Express request
 * @param {Object} res - Express response
 * @param {Function} next - Next middleware
 */
function cacheMiddleware(req, res, next) {
  // Skip caching for non-GET and non-POST requests
  if (!['GET', 'POST'].includes(req.method)) {
    return next();
  }
  
  // Skip caching if cache control header is set to no-cache
  if (req.headers['cache-control'] === 'no-cache') {
    return next();
  }
  
  // Skip for certain endpoints
  if (req.originalUrl.includes('/set-options') || req.originalUrl.includes('/clear-cache')) {
    return next();
  }
  
  // Create cache key
  const cacheKey = createCacheKey(req);
  
  // Check if we have a cached response
  if (responseCache.has(cacheKey)) {
    const cachedResponse = responseCache.get(cacheKey);
    
    // Check if cache entry is still valid
    if (Date.now() - cachedResponse.timestamp < CACHE_TTL) {
      // Return cached response
      return res.status(200).json({
        ...cachedResponse.data,
        cached: true,
        cacheAge: Math.round((Date.now() - cachedResponse.timestamp) / 1000)
      });
    } else {
      // Remove expired cache entry
      responseCache.delete(cacheKey);
    }
  }
  
  // Capture the original json method
  const originalJson = res.json;
  
  // Override the json method to cache the response
  res.json = function (data) {
    // Only cache successful responses
    if (res.statusCode === 200 && data && data.success) {
      // Store in cache
      responseCache.set(cacheKey, {
        data,
        timestamp: Date.now()
      });
      
      // Clean cache if needed
      if (responseCache.size > MAX_CACHE_SIZE) {
        cleanCache();
      }
    }
    
    // Call the original json method
    return originalJson.call(this, data);
  };
  
  next();
}

/**
 * Rate limiting middleware
 * @param {string} endpointType - Type of endpoint
 * @returns {Function} Middleware function
 */
function rateLimitMiddleware(endpointType) {
  return (req, res, next) => {
    // Skip rate limiting for certain IPs (e.g., localhost)
    if (req.ip === '127.0.0.1' || req.ip === '::1') {
      return next();
    }
    
    const now = Date.now();
    
    // Get rate limit data for this IP
    if (!rateLimitStore.has(req.ip)) {
      rateLimitStore.set(req.ip, {});
    }
    
    const ipLimits = rateLimitStore.get(req.ip);
    
    // Initialize endpoint limit if not exists
    if (!ipLimits[endpointType]) {
      ipLimits[endpointType] = {
        windowStart: now,
        count: 0
      };
    }
    
    const endpointLimit = ipLimits[endpointType];
    const limitConfig = rateLimits[endpointType];
    
    // Reset the window if it has expired
    if (now - endpointLimit.windowStart > limitConfig.windowMs) {
      endpointLimit.windowStart = now;
      endpointLimit.count = 0;
    }
    
    // Check if we're over the limit
    if (endpointLimit.count >= limitConfig.maxRequests) {
      return res.status(429).json({
        success: false,
        error: 'Too many requests, please try again later',
        retryAfter: Math.ceil((endpointLimit.windowStart + limitConfig.windowMs - now) / 1000)
      });
    }
    
    // Increment the counter
    endpointLimit.count++;
    
    // Add rate limit headers
    res.setHeader('X-RateLimit-Limit', limitConfig.maxRequests);
    res.setHeader('X-RateLimit-Remaining', limitConfig.maxRequests - endpointLimit.count);
    res.setHeader('X-RateLimit-Reset', Math.ceil((endpointLimit.windowStart + limitConfig.windowMs) / 1000));
    
    next();
  };
}

/**
 * Z3 solver optimization middleware
 * @param {Object} req - Express request
 * @param {Object} res - Express response
 * @param {Function} next - Next middleware
 */
function optimizeSolverMiddleware(req, res, next) {
  try {
    // Check if getSolverInstanceStats exists before calling it
    if (typeof z3Service.getSolverInstanceStats === 'function') {
      // Auto-cleanup of solver instances based on system load
      const stats = z3Service.getSolverInstanceStats();
      
      // If we have a lot of instances, reduce the max instances and max age
      if (stats.totalInstances > 40) {
        z3Service.setMaxSolverInstances(30);
        z3Service.setSolverInstanceMaxAge(15 * 60 * 1000); // 15 minutes
      } else if (stats.totalInstances < 10) {
        // If we have few instances, increase the limits
        z3Service.setMaxSolverInstances(50);
        z3Service.setSolverInstanceMaxAge(30 * 60 * 1000); // 30 minutes
      }
    } else {
      // Log a warning but continue execution
      console.warn('z3Service.getSolverInstanceStats is not available - skipping solver optimization');
    }
  } catch (error) {
    // Log error but don't interrupt request processing
    console.error('Error in optimizeSolverMiddleware:', error.message);
  }
  
  next();
}

/**
 * Middleware to clear response cache
 * @param {Object} req - Express request
 * @param {Object} res - Express response
 */
function clearCache(req, res) {
  responseCache.clear();
  res.status(200).json({
    success: true,
    message: 'Cache cleared successfully'
  });
}

/**
 * Middleware to get performance statistics
 * @param {Object} req - Express request
 * @param {Object} res - Express response
 */
function getPerformanceStats(req, res) {
  const solverStats = z3Service.getSolverInstanceStats();
  
  res.status(200).json({
    success: true,
    stats: {
      cache: {
        size: responseCache.size,
        maxSize: MAX_CACHE_SIZE,
        ttl: CACHE_TTL
      },
      rateLimits,
      solver: solverStats,
      memory: process.memoryUsage()
    }
  });
}

module.exports = {
  cacheMiddleware,
  rateLimitMiddleware,
  optimizeSolverMiddleware,
  clearCache,
  getPerformanceStats
}; 