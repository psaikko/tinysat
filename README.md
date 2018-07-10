# tinysat

Tinysat is a minimal SAT solver written in javascript which implements

- The CDCL algorithm
- First unique implication point (1UIP) clause learning
- Two watched literal scheme for unit propagation

Tinysat can be run with node.js or in the browser:

``
node tinysat_node.js <dimacs cnf file>
``
