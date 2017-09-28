"use strict";

const TRUE = 1;
const UNDEF = 0;
const FALSE = -1;

const SAT = 10;
const UNSAT = 11;
const UNKNOWN = 12;

const prop_budget = 500000;
const conf_budget = 50000;

var initSolver = function () {

	var logger = function(s) { console.log(s); };
	//logger = function(s) { };
	var litVar = Math.abs;

	var clauses = [];
	var origClauses = 0;

	var propQueue = [];
	var propInd = 0;

	var assignment = []
	var assignLevel = []
	var assignReason = []

	var assignStack = []

	var level = 0;

	var propagations = 0;
	var conflicts = 0;
	var decisions = 0;

	var swap = function (arr, i, j) {
		var t = arr[i];
		arr[i] = arr[j];
		arr[j] = t;
	}

	var arrayToString = function(arr) {
		var s = "[";
		for (var i = 0; i < arr.length; ++i) {
			s += arr[i];
			if (i != arr.length - 1) s += ",";
		}
		s += "]";
		return s;
	}

	var conflictToString = function(arr) {
		var s = "[";
		for (var i = 0; i < arr.length; ++i) {
			s += arr[i]+"@"+assignLevel[litVar(arr[i])];
			if (i != arr.length - 1) s += ",";
		}
		s += "]";
		return s;
	}

	var isWhitespace = function(c) {
		return (c == '\t') || (c == '\n') || (c == ' ');
	}

	var skipWhitespace = function (text, i) {
		while (i < text.length && isWhitespace(text[i])) ++i;
		return i;
	}

	var litPolarity = function (lit) {
		return lit < 0 ? FALSE : TRUE;
	}

	var assignmentToString = function () {
		var s = "";
		for (var i = 1; i < assignment.length; ++i) {
			if (assignment[i] == UNDEF) {
				s += i+"U";
			} else if (assignment[i] == FALSE) {
				s += i+"F@"+assignLevel[i];
			} else {
				s += i+"T@"+assignLevel[i];
			}
			if (i < assignment.length - 1) s += ",";
		}
		return s;
	}

	// parse cnf format instance
	var parse = function (text) {
		logger("parse input");
		var i = 0;
		var maxVar = 0;
		while (i < text.length) {
			i = skipWhitespace(text, i);
			if (i == text.length) break;

			if (text[i] == 'c') {
				while(text[i++] != '\n' && i < text.length) ;
			} else if (text[i] == 'p') {
				while(text[i++] != '\n' && i < text.length) ;
			} else {
				var clause = []
				var lit = 0;
				while (i < text.length) {
					var j = 0;
					while (!isWhitespace(text[i+j]) && i+j < text.length)
						++j;
					lit = parseInt(text.substring(i, i+j))
					if (lit != 0) {
						maxVar = Math.max(maxVar, litVar(lit))
						clause.push(lit);
						i = skipWhitespace(text, i+j);
					} else {
						i += j;
						break;
					}
				}
				clauses.push(clause)
			}
		}

		for (var j = 0; j <= maxVar; ++j) {
			assignment.push(0);
			assignLevel.push(null);
			assignReason.push(null);
		}
		origClauses = clauses.length;
	}

	var pushAssignment = function (lit, reason) {
		var v = litVar(lit);
		assignment[v] = litPolarity(lit);
		assignLevel[v] = level;
		assignReason[v] = reason;
		assignStack.push(v);

		propQueue.push({
			lit    : lit,
			reason : reason
		});
	}

	// remove all assignments and consequences after dl lnew
	var popAssignments = function (lnew) {
		logger("backjump to level "+lnew);

		while (true) {
			var backVar = litVar(assignStack[assignStack.length - 1]);
			if (assignLevel[backVar] > lnew) {
				assignment[backVar] = UNDEF;
				assignReason[backVar] = null;
				assignLevel[backVar] = null;
				assignStack.pop();
			} else {
				break;
			}
		}
		level = lnew;
	}

	// propagate assignments in propQueue
	var propagate = function () {
		// TODO: 2WL
		logger("propagate");
		var seen = {};
		while (propInd < propQueue.length) {
			var p = propQueue[propInd];
			var pv = litVar(p.lit);
			logger("propagating "+p.lit+"@"+level+" from "+arrayToString(p.reason));
			propInd++;

			var sat_clauses = 0;
			nextclause: for (var i = 0; i < clauses.length; ++i) {
				var unsats = 0;
				var undefs = 0;
				var j_undef = 0;
				for (var j = 0; j < clauses[i].length; ++j) {
					var l = clauses[i][j];
					var a = assignment[litVar(l)];
					if (a == UNDEF) {
						++undefs;
						if (undefs > 1) continue nextclause;
						j_undef = j;
					} else if (a == litPolarity(l)) {
						++sat_clauses;
						continue nextclause;
					} else if (a != litPolarity(l)) {
						++unsats;
					}
				}

				if (unsats == clauses[i].length) {
					++conflicts;
					logger("conflict "+arrayToString(clauses[i]));
					propQueue = [];
					propInd = 0;
					return {
						conflict:clauses[i]
					};
					break;
				} else if (unsats == clauses[i].length - 1 &&
					         !seen[clauses[i][j_undef]]) {
					seen[clauses[i][j_undef]] = true;
					pushAssignment(clauses[i][j_undef], clauses[i]);
					++propagations;
					logger("enqueue " + clauses[i][j_undef] +
											" from " + arrayToString(clauses[i]));
				}
			}

			if (sat_clauses == clauses.length)
				return { sat: true };
		}
		propQueue = [];
		propInd = 0;
		return {};
	}

	const first_uip = true;

	// TODO: fix this
	var analyze_1uip = function (conflict) {
		logger("analyze "+conflictToString(conflict));

		if (level == 0) return [];

		var seen = {};
		var i_stack = assignStack.length - 1;

		var clause = [];
		var assertingLits = 0;

		var lit = null;
		var v = null;
		var reason = conflict;

		do {
			for (var i = 0; i < reason.length; ++i) {
				var vi = litVar(reason[i]);
				if (!seen[vi] && vi != v && assignLevel[vi] > 0) {
					seen[vi] = true;
					if (assignLevel[vi] == level) {
						console.log(reason[i]+" deferred");
						++assertingLits;
					} else {
						console.log(reason[i]+" included");
						clause.push(reason[i]);
					}
				}
			}

			while (!seen[litVar(assignStack[i_stack])]) --i_stack;

			lit = assignStack[i_stack];
			--i_stack;
			v = litVar(lit)
			reason = assignReason[v];
			seen[v] = false;
			--assertingLits;

			logger(lit+" from "+conflictToString(reason));
		} while (assertingLits > 0);

		clause.push(-lit);
		swap(clause, 0, clause.length-1);

		logger("learn clause "+conflictToString(clause)+" at l"+level);
		return clause;
	}

	var analyze = function (conflict) {
		logger("analyze");
		// TODO: learn 1UIP
		var clause = [];
		var stack = [];
		var seen = {};

		for (var i = 0; i < conflict.length; ++i) {
				stack.push(conflict[i]);
				seen[conflict[i]] = true;
		}

		while (stack.length > 0) {
			var l = stack.pop();
			var v = litVar(l);
			var reason = assignReason[v];

			if (reason.length == 0) {// l was a decision
				clause.push(l);
			} else {
		  	for (var i = 0; i < reason.length; ++i)
		  		if (!seen[reason[i]] && litVar(reason[i]) != v) { // add implying assignment to stack
		  			stack.push(reason[i]);
		  			seen[reason[i]] = true;
		  		}
			}
		}

		// move asserting literal to front
		for (var i = 0; i < clause.length; ++i) {
			if (assignLevel[litVar(clause[i])] > assignLevel[litVar(clause[0])]) {
				swap(clause, i , 0);
			}
		}

		logger("learn clause "+conflictToString(clause)+" at l"+level);
		return clause;
	}

	var decision = function () {
		// TODO: VSIDS
		for (var i = 1; i < assignment.length; ++i) {
			if (assignment[i] == UNDEF) {
				++decisions;
				logger("decision "+i);
				return i;
			}
		}
	}

	var cdcl = function () {
		// TODO: restarts
		logger("init cdcl")
		while (true) {
			if (propagations > prop_budget ||
					conflicts > conf_budget) {
				logger("budget exceeded");
				return { status: UNKNOWN };
			}
			logger("- - - - - - - - - - -");
			var res = propagate();
			if (res.conflict) {
				var learnt = analyze(res.conflict);
				if (learnt.length == 0)
					return {
						status: UNSAT
					};
				clauses.push(learnt);

				var popTo = 0;
				for (var i = 0; i < learnt.length; ++i) {
					var i_level = assignLevel[litVar(learnt[i])];
					if (i_level != level);
						popTo = Math.max(popTo, i_level - 1);
				}

				popAssignments(popTo);
				// by convention first literal is asserting
				pushAssignment(learnt[0], learnt);
			} else if (res.sat) {
				logger("assignment "+assignmentToString());
				return {
					status: SAT,
					model: assignment
				};
			} else {
				++level;
				pushAssignment(decision(), []);
			}
		}
	}

	return {
		logger:logger,
		parse:parse,
		solve:cdcl
	}
};

var solve = function () {

	document.getElementById('txt_result').value = "";

	var t_start = (new Date()).getTime();
	var text = document.getElementById('txt_wcnf').value;
	var solver = initSolver();
	solver.parse(text);
	var result = solver.solve();
	var t_end = (new Date()).getTime();

	document.getElementById('txt_result').value +=
		"c "+(t_end - t_start)+"ms\n";

	if (result.status == SAT) {
		solver.logger("satisfiable");
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
		solver.logger("unsatisfiable");
		document.getElementById('txt_result').value += "s UNSATISFIABLE\n";
	} else {
		solver.logger("aborted");
		document.getElementById('txt_result').value += "s UNKNOWN\n";
	}
}

document.getElementById("btn_solve").onclick = solve;