'use strict';

var p = require('path')
var util = require('util')
var Promise = require('bluebird')
var plugins = require('./lib/plugins.js')
var routes = require('./routes')
var middlewares = require('./middlewares')
var parallelMiddlewares = require('./lib/utils.js').parallelMiddlewares

var fs = Promise.promisifyAll(require('fs'))
var debug = require('debug')('explorer:server')

module.exports = function(app) {
  var config = app.get('config');

  config.upload.path = p.join(app.get("root"),config.upload.path);

  let cache = require('./lib/cache')({
    cache : "memory"
  });

  app.set('cache', function getCache(namespace) {
      return new cache(namespace)
  })

  plugins.registerPlugins(app)


  app.use(function(req, res, next) {
    req.config = config;

    res.locals.app_root = config.app_root ? config.app_root : '/'

    res.locals.messages = {
      info: req.flash('info'),
      error: req.flash('error')
    }

    res.locals.upload = config.upload

    return next()
  })

  app.use(function(req, res, next) {
    return next()
  });

  app.use(parallelMiddlewares([
    middlewares.format(app),
    middlewares.optionsCookie
  ]))

  app.use(middlewares.registerHooks(app))

  //register plugins routes
  plugins.registerPluginsRoutes(app)

  //Load routes
  routes.Tree(app);

  return Promise.resolve(app)
}
