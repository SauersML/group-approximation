---
rg: 2
id: nonhyperlinear-from-dimension-reported-schur-compiler
kind: route
title: Diagonalize the witness dimension and activate its supercritical Schur table
target: non-hyperlinear-group
requires:
  - dimension-matched-kleene-microstate-diagonal
  - dimension-reported-schur-replica-halting-compiler
  - approximate-schur-replicas-force-exponential-dimension
---

Apply the dimension-matched Kleene lemma to the compiler.  On a halting output
`D`, the compiler selects `N` by `(DRC1)` and the robust replica theorem rules
out the very `D`-dimensional marked witness which caused the fixed-point
machine to halt.  Therefore the fixed-point machine never halts, its compiled
mark is nontrivial, and hyperlinearity would contradict that nonhalting by
producing a searchable marked microstate.

