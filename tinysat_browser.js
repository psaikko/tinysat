"use strict";

var solve = function () {

  document.getElementById('txt_result').value = "";

  var t_start = (new Date()).getTime();
  var text = document.getElementById('txt_wcnf').value;
  var solver = initSolver();

  var prop_budget = parseInt(document.getElementById('txt_prop').value);
  var conf_budget = parseInt(document.getElementById('txt_conf').value);
  var time_budget = parseInt(document.getElementById('txt_time').value);

  var use_1uip = document.getElementById('chk_1uip').checked;
  var use_2wl = document.getElementById('chk_2wl').checked;

  var logger;
  if (document.getElementById('chk_log').checked) {
    logger = console.log;
  } else {
    logger = function(s) { };
  }

  solver.parse(text);
  var result = solver.solve(logger, prop_budget, conf_budget, time_budget, use_2wl, use_1uip);
  var t_end = (new Date()).getTime();

  document.getElementById('txt_result').value +=
    "c "+(t_end - t_start)+"ms\n";

  if (result.status == SAT) {
    logger("satisfiable");
    var vline = "v"
    for (var i = 1; i < result.model.length; ++i) {
      if (result.model[i] == TRUE) {
        vline += " "+i;
      } else if (result.model[i] == FALSE) {
        vline += " -"+i;
      }
    }
    vline += "\n";
    document.getElementById('txt_result').value += "s SATISFIABLE\n";
    document.getElementById('txt_result').value += vline;
  } else if (result.status == UNSAT) {
    logger("unsatisfiable");
    document.getElementById('txt_result').value += "s UNSATISFIABLE\n";
  } else {
    logger("aborted");
    document.getElementById('txt_result').value += "s UNKNOWN\n";
  }
}

document.getElementById("btn_solve").onclick = solve;