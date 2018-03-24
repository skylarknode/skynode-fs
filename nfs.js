'use strict';
const _fs = require('fs-extra');
const _chokidar = require('chokidar');
const _diskspace = require('diskspace');

var p = require('path');
var Promise = require('bluebird');
var util = require('util');
var fs = Promise.promisifyAll(require('fs'));
var HTTPError = require('./HTTPError.js');
var async = require('async');
var mime = require('mime');
var moment = require('moment');
var crypto = require('crypto');
const mkdirp = require('mkdirp');
const rmdirp = require('rmdirp');

var MODE_0666 = parseInt('0666', 8);
var MODE_0755 = parseInt('0755', 8);


var rimraf = Promise.promisify(require('rimraf'));

/**
 * Filter names starting with a dot
 * @param string f
 * @return bool
 */
var noDotFiles = function(f) { 
  return !/^\./.test(p.basename(f)) 
}

/**
 * Secures a string for a command line search
 * strips: ", ', \, &, |, ;, -
 * @param string str
 * @return string
 */
var secureString = function secureString(str) {
  return str.replace(/"|'|\\|&|\||;|-/g, '')
}

/**
 * Get pack the higher available path to avoid unwanted behaviors
 * @param string root - usually req.user.home
 * @param string path - the path we want to go to
 * @return string - the higher path \o/
 */
var higherPath = function(root, path) {

  if(!root && typeof root != 'string')
    throw new TypeError('Root is not a string')

//  root = p.resolve(root)
  path = p.resolve(root, p.normalize(path) || './')

  if(path.length < root.length || path.indexOf(root) == -1) {
    path = root
  }

  return path
}

/**
 * Just wanted to test ES6 new stuff
 * ... just kidding extend one arg to another instead of only the first one
 * @param object origin
 * @param object ...add
 * @return origin
 */
var extend = function() {
  var add = [].slice.call(arguments)
  var origin = add.shift()

  for(let i in add) {
    origin = util._extend(origin, add[i]) 
  }

  return origin
}

/**
 * Build an URL string from params
 * this is used by the view to generate correct paths according to 
 * the sort, order, pages, search etc.
 * @param string path
 * @param string search
 * @param object options - will be built to a query key=value
 */
var buildUrl = function(path, search, options) {

  var str = ''
  var first = true

  for(let i in options) {
    if(options[i]) {
      str += first ? '?' : '&'
      str += i + '=' + options[i]
      first = false
    }
  }

  if(search) {
    return '/search' + str + '&search=' + search + '&path=' + encodeURIComponent(p.normalize(path))
  }

  return '/' + str + '&path=' + encodeURIComponent(p.normalize(path))
}

/**
 * Sanitize a string 
 * @see https://github.com/ezseed/watcher/blob/master/parser/movies.js#L27
 * @param string path
 */
var sanitize = function(path) {
  return p.basename(path)
     .replace(p.extname(path), '')
     .replace(new RegExp('-[a-z0-9]+$', 'i'), '') //team name
     .replace(/\-|_|\(|\)/g, ' ') //special chars
     .replace(/([\w\d]{2})\./ig, "$1 ") //Replacing dot with min 2 chars before
     .replace(/\.\.?([\w\d]{2})/ig, " $1")  //same with 2 chars after
     .replace(/part\s?\d{1}/ig, '') //part
     .replace(/\[[a-z0-9]+\]$/i, '')
     .replace(new RegExp(' {2,}', 'g'), ' ') //double space
}

/**
 * fs.exists is deprecated
 */
var exists = function(path) {
  return new Promise(function(resolve, reject) {
    fs.access(path, fs.F_OK, function(err) {
      return resolve(err ? false : true)
    })
  })
}

/**
 * fs.existsSync is deprecated
 */
var existsSync = function(path) {
  var exists = false

  try {
    fs.accessSync(path, fs.F_OK)
    exists = true
  } catch(e) {}

  return exists
}

/**
 * firstExistingPath
 * Get back the first path that does exist
 * @param array paths 
 * @return string the founded path
 */
var firstExistingPath = function(paths) {
  for(let i in paths) {
    if(paths[i] && existsSync(paths[i])) {
      return paths[i]
    }
  }

  return false
}

/**
 * Remove directory content with rimraf on each file
 * Skips dot files
 * @todo test?
 * @param string path
 * @return Promise
 */
var removeDirectoryContent = function(path) {
  return fs.readdirAsync(path)
  .filter(noDotFiles)
  .map(function(filename) {
    return rimraf(p.resolve(path, filename))
  })
}

/**
 * Handles system error, usually a Promise.catch
 * @param function next middleware next
 * @return function called by a Promise.catch
 */
var handleSystemError = function(next) {
   return function(e) {
   
     console.error(e.stack)

     return next(new HTTPError('A server error occur, if this happens again please contact the administrator: '+e.message, 500))
   }  
}

/**
 * Handles middlewares in parallel
 */
var parallelMiddlewares = function(middlewares) {
  return function(req, res, next) {
    return async.each(middlewares, function(m, cb) {
      return m(req, res, cb) 
    }, next) 
  }
}

/**
 * Give path informations
 * @param string path
 */
var pathInfo = function(path) {

  var filename = p.basename(path) 

  var o = {
    name: filename,
    ext: p.extname(filename),
    dirname: p.dirname(path),
    path: path
  }

  var m = mime.lookup(o.path).split('/')

  o.type = m[0]
  
  var filetype = m[1]
  
  if(~['.zip', '.rar', '.iso', '.tar'].indexOf(o.ext)) {
    o.type = 'archive'
  }

  if(!~['application', 'video', 'audio', 'image', 'text', 'archive'].indexOf(o.type)) {
    o.type = 'application'
  }

  return Promise.resolve(o) 
}

/**
 * create sha1 hash from a string
 * @param string str the string to hash
 * @return string a sha1 hash in hexadecimal
 */
var sha1Hash = function(str) {
  var shasum = crypto.createHash('sha1')

  shasum.update(str, 'utf8')

  return shasum.digest('hex')
}


const DATE_FORMAT = 'llll'

const DEFAULT_STAT = {
  directory: false, 
  type: 'unknown',
  size: 0,
  mtime: 0,
  lastModified: '',
  atime: 0,
  lastAccessed: '',
  ctime: 0,
  lastChanged: '',
  depth: 0
}

var gracefulCatch = function(root, path) {
  return function(err) {

    if(err.code != 'EACCES' && err.code != 'ENOENT') {
      return Promise.reject(err)
    }

    if(err.code == 'EACCES')
      console.error('No file access (check rights on %s)', path)
    else
      console.error('No file entry (file %s does not exist ?!)', path)

    return Promise.resolve(root)
  }
}

/**
 * Build Breadcrumb from paths
 * @param string root
 * @param string path
 * @return array of objects {path, name} where name will be linked to path
 */
var buildBreadcrumb = function(root, path) {
  var breadcrumbs = [{path: root, name: root}]

  if(!path) {
    return breadcrumbs;
  }

  let paths = path.replace(root, '')
    .split('/')
    .filter(function(v) { return v != '' })

  for(let i in paths) {
    breadcrumbs[parseInt(i)+1] = {
      path: p.join(breadcrumbs[i].path, paths[i]),
      name: paths[i]
    }
  }

  return breadcrumbs
}

/**
 * @param string file
 * @param object root (@see pathInfo)
 * @param object options:
 *   - int maxDepth (10)
 *   - function filter (@see noDotFiles)
 */
var directorySize = function(file, root, options) {

  var path = p.resolve(root.path, file)
  var depth = file.split(p.sep).length

  if(root.depth < depth) {
    root.depth = depth
  }

  if(root.depth >= options.maxDepth) {
    root.depth = Infinity 
    return Promise.resolve(root)
  }

  return fs.statAsync(path).then(function(stat) {
    if(stat.isDirectory()) {
      let items = fs.readdirAsync(path);

      for(let i in options.filters) {
        items = items.filter(options.filters[i]) 
      }

      return items.each(v => directorySize(p.join(file, v), root, options));
    } else {
      root.size += stat.size
      return Promise.resolve(root)
    }
  }) 
  .catch(gracefulCatch(root, path))
}

var recursiveReaddir = function(root, options) {

  let items =  fs.readdirAsync(root);

  for(let i in options.filters) {
    items = items.filter(options.filters[i])
  }

  return items.map(function(f) {
    var path = p.join(root, f)

    return fs.statAsync(path).then(function(stat) {
      let depth = root.replace(options.root, '').split(p.sep).length;

      if(depth > options.maxDepth)
        return path

      if(stat.isDirectory()) {
        return recursiveReaddir(path, options) 
      }

      return path
    })
    .catch(gracefulCatch(root, path))
  }).then(function(paths) {
    paths.push(root)
    return [].concat.apply([], paths)
  })
}

/**
 * Get directory size through cache
 * @param object options
 * @return function
 */
var getDirectorySize = function(options) {
  var cache = options.cache || false;

  /**
   * @param object file (see below)
   * @return Promise
   */
  return function calcDirectorySize(f) {

    if(f.ext !== 'app' && f.directory !== true) {
      return f
    }

    var hash = sha1Hash(f.path);

    var resolver = function() {
      if(cache) {
        return Promise.all([
          cache.time.put(hash, ''+f.mtime, options.cacheTTL),
          cache.size.put(hash, ''+f.size, options.cacheTTL)
        ]) .then(function() {
          return f;
        })
      }

      return f;
    }

    if(cache) {
      return cache.time.get(hash).then(function(cached) {
        if(cached == f.mtime) {
          return cache.size.get(hash)
          .then(function(size) {
            f.size = parseInt(size)
            return f
          })
        }

        return directorySize('', f, options).then(resolver);
      })
    }

    return directorySize('', f, options).then(resolver)
  }
}

/**
 * Handles path argument and return filtered paths
 * @param mixed path
 * @param Object options {recursive: boolean}
 * @return array Promises
 */
var paths = function(path, options) {
  let items

  if(typeof path == 'string') {
    if(options.recursive === true) {
      return recursiveReaddir(path, options).map(function(e) {
        return p.relative(path, e);
      })
    }  
    
    items = fs.readdirAsync(path);
  } else if(Array.isArray(path)) {
    items = Promise.all(path);
  } else {
    throw new TypeError('Path must be an array or a string')
  }

  for(let i in options.filters) {
    items = items.filter(options.filters[i]);
  }

  return items;
}

var stat = function(path) {
    return fs.statAsync(path).then(function(stat) {
      var info = {
        name: p.basename(path),
        mimeType: mime.lookup(path),
        ext: p.extname(path),
        dirname: p.dirname(path),
        path: path,
        size : stat.size,
        mtime :  stat.mtime.getTime(),
        lastModified : moment(stat.mtime).format(DATE_FORMAT),
        atime : stat.atime.getTime(),
        lastAccessed : moment(stat.atime).format(DATE_FORMAT),
        ctime : stat.ctime.getTime(),
        lastChanged : moment(stat.ctime).format(DATE_FORMAT),
      };

      if(stat.isDirectory()) {
        info.directory = true;
        info.depth = 0;
        info.type = 'directory';
      } else {
        info.type = "file"
      }

      return info;
    });
};

var statSync = function(path) {
    var stat =  fs.statSync(path),
        info = {
        name: p.basename(path),
        mimeType: mime.lookup(path),
        ext: p.extname(path),
        dirname: p.dirname(path),
        path: path,
        size : stat.size,
        mtime :  stat.mtime.getTime(),
        lastModified : moment(stat.mtime).format(DATE_FORMAT),
        atime : stat.atime.getTime(),
        lastAccessed : moment(stat.atime).format(DATE_FORMAT),
        ctime : stat.ctime.getTime(),
        lastChanged : moment(stat.ctime).format(DATE_FORMAT),
    };

    if(stat.isDirectory()) {
      info.directory = true;
      info.depth = 0;
      info.type = 'directory';
    } else {
      info.type = "file"
    }

    return info;
};

/*
 * Reads EXIF data
 */
function readExif(path, mime) {
  mime = mime || '';

  let _read = function defaultRead(resolve, reject) {
    resolve(null);
  };

  if ( mime.match(/^image/) ) {
    try {
      _read = function exifRead(resolve, reject) {
        /*eslint no-new: "off"*/
        new require('exif').ExifImage({image: path}, (err, result) => {
          if ( err ) {
            reject(err);
          } else {
            resolve(JSON.stringify(result, null, 4));
          }
        });
      };
    } catch ( e ) {}
  }

  return new Promise(_read);
}

/*
 * Create a read stream
 */
function createReadStream(filename, options) {
  return new Promise((resolve, reject) => {
    /*eslint new-cap: "off"*/
    try {
      const stream = _fs.createReadStream(filename, Object.assign({
        bufferSize: 64 * 1024
      }, options));

      stream.on('error', (error) => {
        reject(error);
      });
      stream.on('open', () => {
        resolve(stream);
      });
    } catch ( e ) {
      reject(e);
    }
  });
}

/*
 * Create a write stream
 */
function createWriteStream(filename, options) {
  return new Promise((resolve, reject) => {
    /*eslint new-cap: "off"*/
    try {
      const stream = _fs.createWriteStream(filename);

      stream.on('error', (error) => {
        reject(error);
      });
      stream.on('open', () => {
        resolve(stream);
      });
    } catch ( e ) {
      reject(e);
    }
  });
}

/*
 * Creates watch
 */
function createWatch(dir, callback) {

  _chokidar.watch(dir, {ignoreInitial: true, persistent: true}).on('all', (evname, wpath) => {
    if ( ['change', 'error'].indexOf(evname) === -1 ) {
      try {

        callback(dir,  {
          event:  evname,
          real: wpath
        });
      } catch ( e ) {
        console.warn(e, e.stack);
      }
    }
  });
}

function quoat(path) {

  return new Promise(function (resolve, reject) {
    _diskspace.check(path, (err, result) => {
      //result.total is how much the drive has totally.
      //result.used is how much of the drive is reported as used.
      //result.free is how much free space you have.
      //result.status isn't really that useful unless you want to debug.
      resolve(result);
    });
  });
}

/**
 * Mkdir -p.
 *
 */
function mkdir(path,  opts ) {
  opts = opts || MODE_0755;
  return new Promise(function (resolve, reject) {
    mkdirp(path, opts, function(err,result) {
        if (err) {
          reject(err);
        } else {
          resolve(result);
        }
    });
  });
}

function mkdirSync(path,  opts ) {
  opts = opts || MODE_0755;
  return mkdirp.sync(path, opts);
}

/**
 * Rmdir -p.
 *
 */
function rmdir(path ) {
  return new Promise(function (resolve, reject) {
    rmdirp(path, function(err,result) {
        if (err) {
          reject(err);
        } else {
          resolve(result);
        }
    });
  });
}

function rmdirSync(path ) {
  return rmdirp.sync(path);
}

/**
 * Check if the given directory `path` is empty.
 */

function checkEmpty(path, fn) {
  return new Promise(function (resolve, reject) {
    fs.readdir(path, function(err, files) {
        if (err && err.code !== 'ENOENT') {
          reject(err);
        } else {
          resolve(!files || !files.length);
        }
    })
  });
}


function write(path, str, mode) {
    return fs.writeFileSync(path, str, { mode: mode || MODE_0666 })
}

function writeSync(path, str, mode) {
    return fs.writeFileSync(path, str, { mode: mode || MODE_0666 })
}


function read(path) {
    return fs.readFileAsync(path, 'utf8');
}
function readSync(path) {
    return fs.readFileSync(path, 'utf8');
}

module.exports = {
  noDotFiles: noDotFiles,
  higherPath: higherPath,
  extend: extend,
  buildUrl: buildUrl,
  sanitize: sanitize,
  secureString: secureString,
  firstExistingPath: firstExistingPath,
  removeDirectoryContent: removeDirectoryContent,
  handleSystemError: handleSystemError,
  parallelMiddlewares: parallelMiddlewares,
  pathInfo: pathInfo,
  sha1Hash: sha1Hash,
  exists: exists,
  existsSync: existsSync,

  DATE_FORMAT : DATE_FORMAT, 
  DEFAULT_STAT : DEFAULT_STAT,
  W_OK : fs.W_OK,

  createReadStream : createReadStream,
  createWriteStream : createWriteStream,
  createWatch: createWatch,



  buildBreadcrumb : buildBreadcrumb,
  directorySize : directorySize,
  getDirectorySize : getDirectorySize,
  gracefulCatch : gracefulCatch,
  paths : paths,
  
  
  readExif : readExif,
  recursiveReaddir : recursiveReaddir,


  quoat : quoat,

  stat : stat,
  statSync : statSync,

  mkdir: mkdir,
  mkdirSync: mkdirSync,

  rmdir: rmdir,
  rmdirSync: rmdirSync,

  read: read,
  readSync: readSync,

  write: write,
  writeSync: writeSync
}
