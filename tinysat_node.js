tinysat = require('./tinysat_core.js')

var fs = require('fs')
var instancefile = process.argv[2];

var solver = tinysat.initSolver();

fs.readFile(instancefile, 'ascii', function(err, data) {
  if (err) throw err;
  solver.parse(data);
  result = solver.solve();

  if (result.status == tinysat.status.SAT) {
    console.log("s SATISFIABLE");
    var model_line = "v"
    for (var v = 1; v < result.model.length; v++) {
      if (result.model[v] > 0) {
        model_line += " "+v;
      } else {
        model_line += " -"+v;
      }
    }
    console.log(model_line);
  } else if (result.status == tinysat.status.UNSAT) {
    console.log("s UNSATISFIABLE");
  } else { // UNKNOWN
    console.log("s UNKNOWN");
  }
});