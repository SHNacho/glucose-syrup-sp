# The Glucose SAT Solver

Glucose is based on a new scoring scheme (well, not so new now, it was introduced in 2009) for the clause learning mechanism of so called "Modern" SAT solvers
(it is based our IJCAI'09 paper).
It is designed to be parallel, since 2014.
This page summarizes the techniques embedded in all the versions of glucose.
The name of the Solver name is a contraction of the concept of "glue clauses", a particular kind of clauses that glucose detects and preserves during search.
Glucose is heavily based on Minisat, so please do cite Minisat also if you want to cite Glucose.

-- [Gilles Audemard](http://www.cril.fr/~audemard/) and [Laurent Simon](http://www.labri.fr/perso/lsimon/)
