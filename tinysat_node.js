tinysat = require('./tinysat_core.js')

var fs = require('fs')
var instancefile = process.argv[2];

var logger = null;
var prop_budget = 100000;
var conf_budget = 10000;
var time_budget = 100;
var use_2wl = true;
var use_1uip = true;

var solver = tinysat.initSolver();

fs.readFile(instancefile, 'ascii', function(err, data) {
  if (err) throw err;

  solver.parse(data);
  result = solver.solve(logger, prop_budget, conf_budget, time_budget, use_2wl, use_1uip);

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
    console.log("v "+result.budgets.propagations+" "+result.budgets.conflicts+" "+result.budgets.time);
  }
});