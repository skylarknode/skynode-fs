'use strict';

var fs = require('fs')
var p = require('path')
var moment = require('moment')
var job = require('./job.js')

var debug = require('debug')('explorer:routes:archive')

var Archive = function(router, utils) {
  
  function getData(req) {
    var name = req.body.name || 'archive'+new Date().getTime();
    var temp = p.join(req.options.archive.path || './', name + '.zip')

    return {
      name: name,
      paths: req.options.paths,
      temp: temp,
      directories: req.options.directories
    }
  }

  /**
   * @api {post} /p/archive/action/download Download
   * @apiGroup Plugins
   * @apiName download
   * @apiUse Action
   * @apiSuccess {Stream} zip file attachment
   */
  router.post('/action/download', utils.prepareTree,utils.sanitizeCheckboxes,function(req, res, next) {
    console.log("/action/download started");
    var data = getData(req)

    if(data.paths == 0 && data.directories == 0) {
      return next(new utils.HTTPError('No files to download', 400)) 
    }

    data.stream = res

    var archive = new job(null)
    return archive.create(data, req.user, req.options)
  })

  /**
   * @api {post} /p/archive/action/download Compress (zip)
   * @apiGroup Plugins
   * @apiName compress
   * @apiUse Action
   * @apiSuccess (201) {Object} Created
   */
  router.post('/action/compress',utils.prepareTree, utils.sanitizeCheckboxes,function(req, res, next) {
    if(req.options.archive.disabled)
      return next(new utils.HTTPError('Unauthorized', 401))
  
    var data = getData(req)
  
    if(data.paths == 0 && data.directories == 0) {
      return next(new utils.HTTPError('No files to compress', 400)) 
    }

    data.stream = data.temp
    utils.interactor.send('call', 'archive.create', data, req.user, req.options)
    return res.handle('back', {info: 'Archive created'}, 201)
  })

  return router
}

module.exports = Archive
