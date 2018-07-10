tinysat = require('./tinysat_core.js')

var fs = require('fs')
var instancefile = process.argv[2];

var solver = tinysat.initSolver();

fs.readFile(instancefile, 'ascii', function(err, data) {
  if (err) throw err;
  solver.parse(data);
  console.log(solver.solve());
});