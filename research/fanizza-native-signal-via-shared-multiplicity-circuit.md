---
rg: 2
id: fanizza-native-signal-via-shared-multiplicity-circuit
kind: route
title: Compile the fixed nonlinear menu by shared-multiplicity reversible commutators
target: fanizza-native-signal-groupification
requires:
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
  - fanizza-final-bcs-has-fixed-nonlinear-menu
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
  - fanizza-shared-multiplicity-predicate-circuit-cell
---

Use the exact linear/LCS syntax for all linear flattening constraints.  For
each occurrence of one of the three nonlinear predicate shapes, attach the
fixed cell.  Equation `(CPM2)` turns its reversible gate commutator into the
required conjunction-supported phase, while clause 2 of the cell removes the
only representation-theoretic ambiguity `(CPM4)` in finite matrices.

Clause 1 supplies precisely the weakened HALT completeness condition of
`fanizza-native-signal-groupification`; by `(PIC2)--(PIC3)` fixed packet
multiplicities cause no infinite-dimensional obstruction.  Summing the
finitely many local finite-matrix estimates and the polynomially many linear
flattening losses gives computable `A_m,B_m` in `(NSG1)--(NSG2)`.  Hence all
clauses of the groupification target follow.
