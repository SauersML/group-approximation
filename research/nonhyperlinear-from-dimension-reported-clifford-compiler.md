---
rg: 2
id: nonhyperlinear-from-dimension-reported-clifford-compiler
kind: route
title: Diagonalize the witness dimension against one supercritical Clifford table
target: non-hyperlinear-group
requires:
  - dimension-matched-kleene-microstate-diagonal
  - dimension-reported-clifford-table-halting-compiler
  - marked-clifford-table-exponential-dimension
---

Apply the dimension-matched Kleene lemma.  If its fixed-point search found a
marked microstate of dimension `D`, the halting compiler would activate the
complete table of `E_N` for an `N` satisfying `(MCT3)`.  The same witness would
then violate `(MCT2)`.  Hence the search never halts, `(DMK1)` keeps the mark
nontrivial, and hyperlinearity would make the search halt.  The resulting
finitely presented group is nonhyperlinear.

This route strictly simplifies the replicated Schur route: the reported
dimension itself selects the Pauli rank, so no nonlinear predicate is needed
in the halting payload.
