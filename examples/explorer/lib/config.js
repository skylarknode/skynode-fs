'use strict';
var p = require('path')
var util = require('util')
var mkdirp = require('mkdirp')
var fs = require('fs')
var firstExistingPath = require('./utils.js').firstExistingPath
var existsSync = require('./utils.js').existsSync
var minimist = require('minimist')
var debug = require('debug')('explorer:config')

/**
 * ResolveElement
 * For plugins, make sure they have a path
 * If falsy, set disable: true
 * Creates directory if the element path can't be found
 * @param object element
 * @param object opts defaults
 * @return object
 */
function getResolveElement(config_path) {
  return function(element, opts) {

    if(!opts) { opts = {}}

    if(element === false) {
      element = {disabled: true}
    } else if(element === undefined) {
      element = {}
    }

    if('path' in element) {
      element.path = p.resolve(config_path, element.path || './trash')

      if(!existsSync(element.path)) {
        mkdirp.sync(element.path)
      }
    }

    element = util._extend(opts, element)

    return element
  }
}

/**
 * Load yaml configuration and normalize it
 * @param string config_path
 * @return object configuration
 */
function getConfiguration(config_path) {
  var config = require('yamljs').load(config_path)

  debug('Config from %s', config_path)

  config.config_path = config_path = p.dirname(config_path)

  var resolveElement = getResolveElement(config_path)

  config.plugin_path = p.join(__dirname, '../plugins')

  if(!config.plugins)
    config.plugins = {}

  config.plugins = util._extend(config.plugins, {upload: {}, archive: {}, move: {}})

  if(!config.search) {
    config.search = { method: 'native' }
  }

  if(!config.tree) {
    config.tree = { cache: true }
  }

  config.quiet = !!~process.argv.indexOf('-q') || !!~process.argv.indexOf('--quiet')
  config.auth = config.auth !== undefined ? config.auth : true
  config.user = config.user || false

  if (config.auth === false && !config.user) {
    console.error('Please set a "user" to use without auth.')
    throw new Error('Please set a "user" to use without auth.')
  }

  config.database = p.resolve(config_path, config.database || './data/users')

  if(!config.https) {
    config.https = {}
  }

  config.https.key = p.resolve(config_path, config.https.key || './certs/key.pem')
  config.https.cert = p.resolve(config_path, config.https.cert || './certs/cert.pem')

  config.https = util._extend({
    port: 6859,
    enabled: true
  }, config.https)

  if(!config.port)
    config.port = 4859

  config.remove = resolveElement(config.remove, {
    method: 'mv'
  })

  config.archive = resolveElement(config.archive)
  config.move = resolveElement(config.move)

  config.upload = resolveElement(config.upload, {
    concurrency: 10,
    maxSize: '50mb',
    maxCount: 10
  })

  //not for archive because we want download to work
  if(config.upload.disabled)
    delete config.plugins.upload

  if(config.move.disabled)
    delete config.plugins.move

  config.allowKeyAccess = ['/', '/download', '/search']

  config.cache = config.cache || 'memory'
  config.redis = config.redis || {}

  return config
}

module.exports = function(config_path) {
  var argv = minimist(process.argv.slice(2))

  ;['HOME', 'EXPLORER_CONFIG'].map(function(e) {
    if(!process.env[e])
      process.env[e] = ''
  })

  try {
    config_path = firstExistingPath([
      config_path,
      argv.c,
      p.resolve(process.env.EXPLORER_CONFIG, './config.yml'),
      p.resolve(process.env.HOME || '', './.config/explorer/config.yml'),
      p.resolve(__dirname, '../config.yml'),
      p.resolve(__dirname, '../doc/examples/config.yml')
    ])

    var config = getConfiguration(config_path)
  } catch(e) {
    console.log('No configuration file!')
    throw e
  }

  return config
}
