# tinysat

Tinysat is a minimal SAT solver written in javascript which implements

- The CDCL algorithm
- First unique implication point (1UIP) clause learning
- Two watched literal scheme for unit propagation

Tinysat can be run with node.js

``
node tinysat_node.js <dimacs cnf file>
``

or in the browser

<https://psaikko.github.io/tinysat>
