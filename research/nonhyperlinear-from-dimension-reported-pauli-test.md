---
rg: 2
id: nonhyperlinear-from-dimension-reported-pauli-test
kind: route
title: Diagonalize the witness dimension against a constant-robust Pauli test
target: non-hyperlinear-group
requires:
  - dimension-matched-kleene-microstate-diagonal
  - dimension-reported-pauli-test-halting-compiler
  - pauli-braiding-test-exponential-dimension
---

Apply the dimension-matched Kleene lemma.  If the fixed-point search halted
on a marked witness of dimension `D`, the compiler would activate the Pauli
braiding test at an `N` satisfying `(PBD2)` and turn that same tuple into a
strategy of success at least `1-eta_0`.  The dimension theorem says its local
dimension is strictly larger than `D`, a contradiction.  Hence the search
does not halt, `(DMK1)` keeps the mark nontrivial, and hyperlinearity would
contradict nonhalting by supplying a searchable marked microstate.

