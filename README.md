# Vaphor V2
Array abstraction for Horn clauses 
(variant of SAS2016 Paper Gonnord & Monniaux)

Julien Braine, Laure Gonnord, David Monniaux, 2016-2018
Licence: GPL

Input: a smt2 file produced by hornconverter. (horn clauses with
arrays)
Output: a smt2 file without array variables 
(warnings like Warning : no arguments for composition with head check-sat...
 can be ignored)

Usage: ./vaphor [options] file



Example : ./vaphor demo.smt2 -o demo_2.smt2

Then use your favorite SMT solver to solve the smt2 file.
