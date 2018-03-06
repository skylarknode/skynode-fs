'use strict';
var p = require('path')
var fs = require('fs')
var Router = require('express').Router
var util = require('util')
var existsSync = require('./utils.js').existsSync
var middlewares = require('../middlewares')
var HTTPError = require('./HTTPError.js')

var debug = require('debug')('explorer:plugins')

/**
 * registerPlugins
 * require plugin and call router if it exists
 * called in server.js
 * @see plugins documentation
 * @param Express app
 * @return void sets plugins app.set('plugins')
 */
function registerPlugins(app) {

  var config = app.get('config')
  var cache = app.get('cache')
  var plugins = {}

  for(let name in config.plugins) {
    var e = config.plugins[name]

    var item = p.join(app.get("root"),config.plugin_path, name) 

    try {
      if(e.module) {
        item = p.dirname(require.resolve(e.module))
      }

      console.log('Requiring plugin %s', name)
      plugins[name] = util._extend(require(item), {path: item})


    } catch(e) {

      console.error('Could not require %s', item)

      if(!app.get('is_production'))
        console.error(e.stack)
    }
  }

  app.set('plugins', plugins)
}

function registerPluginsRoutes(app) {

  var config = app.get('config')
  var plugins = app.get('plugins')
  var cache = app.get('cache')
  var allowKeyAccess = config.allowKeyAccess

  for(let name in plugins) {

    var route = '/p/'+ name;

    //move this to another file + require after req.format 
    if('router' in plugins[name]) {

      var router = new Router()

      plugins[name].router(router, {
        prepareTree: middlewares.prepareTree(app),
        HTTPError: HTTPError,
//        tree: tree,
        cache: cache,
        sanitizeCheckboxes : middlewares.sanitizeCheckboxes
      }, config);

      console.log('Using router for plugin %s on %s', name, route)

      try {
        app.use(route, router) 
      } catch(e) {
        console.log('Can not use router for plugin %s!', name) 

       if(!app.get('is_production')){
          console.error(e.stack); 
        }
      }
    }

    var views_path = p.join(plugins[name].path, 'views')

    if(existsSync(views_path)) {
      var views = app.get('views')
      views.push(views_path)
      app.set('views', views)
    } else {
      console.log('No views for plugin %s (%s)', name, views_path)
    }

    if(!('allowKeyAccess' in plugins[name])) {
      continue; 
    } else if(!Array.isArray(plugins[name].allowKeyAccess)) {
      console.error('allowKeyAccess must be an array') 
      continue;
    }
    
    allowKeyAccess = allowKeyAccess.concat(
      plugins[name].allowKeyAccess.map(e => p.join(route, e))
    )
  }

  config.allowKeyAccess = allowKeyAccess

  app.set('config', config)
}

module.exports = {
  registerPlugins: registerPlugins,
  registerPluginsRoutes: registerPluginsRoutes
}
