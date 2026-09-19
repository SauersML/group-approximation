---
rg: 2
id: nonhyperlinear-from-dimension-reported-pauli-test
kind: route
title: Diagonalize the witness dimension against a constant-robust Pauli test
target: non-hyperlinear-group
requires:
  - instance-modulated-kleene-microstate-diagonal
  - dimension-kleene-threshold-needs-amplification-envelope
  - dimension-reported-pauli-test-halting-compiler
  - pauli-braiding-test-exponential-dimension
---

Apply the instance-modulated Kleene lemma. If the fixed-point search halted
on a marked witness of dimension `D`, the compiler would activate the Pauli
braiding test at an `N` satisfying `(PBD2)` and turn that same tuple into a
strategy of success at least `1-eta_0`.  The dimension theorem says its local
dimension is strictly larger than `D`, a contradiction.  Hence the search
does not halt, `(DMK1)` keeps the mark nontrivial, and hyperlinearity would
contradict nonhalting by supplying a searchable marked microstate.

The threshold-envelope requirement explains why the compiler's defect
constant is fixed after the source code is known: an arbitrary positive
`D`-dependent constant would not make the last sentence follow.
