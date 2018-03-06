'use strict';

var fs = require('fs')
var p = require('path')
var moment = require('moment')

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

    //set the archive name
    data.stream.attachment(data.name + '.zip')

    var wfs = req.app.get("wfs");
    wfs.archive(data.paths,data.stream,{});
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


    var wfs = req.app.get("wfs");
    wfs.archive(data.paths,data.tmp,{});

    return res.handle('back', {info: 'Archive created'}, 201)
  })

  return router
}

module.exports = Archive
