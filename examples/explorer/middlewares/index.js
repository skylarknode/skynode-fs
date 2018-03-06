'use strict';
//var trashSize = require('./trashSize.js')
var prepareTree = require('./prepareTree.js')
var sanitizeCheckboxes = require('./sanitizeCheckboxes.js')
var registerHooks = require('./registerHooks.js')
var format = require('./format.js')
var optionsCookie = require('./optionsCookie.js')

module.exports = {
//  trashSize: trashSize,
  prepareTree: prepareTree,
  format: format,
  optionsCookie: optionsCookie,
  sanitizeCheckboxes: sanitizeCheckboxes,
  registerHooks: registerHooks
}
