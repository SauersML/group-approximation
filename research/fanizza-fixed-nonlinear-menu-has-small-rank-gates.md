---
rg: 2
id: fanizza-fixed-nonlinear-menu-has-small-rank-gates
kind: claim
title: Fanizza's three nonlinear predicates need rank matrices of size at most twelve
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
distinct_from:
  fanizza-final-bcs-has-fixed-nonlinear-menu: that identifies the exact finite menu; this constructs and exhaustively verifies compact affine Schur gates for it.
  support-failure-packet-has-explicit-hs-payment: that gives a 2-by-2 gate and exact gap for one binary support failure; this covers the six-variable conditional partition predicate which that packet does not encode.
---

Reduced ordered decision diagrams and `(BDD1)` give the following exact rank
gates for the three nonlinear Fanizza predicate shapes:

```text
predicate                              baseline rank   matrix size
conjunction equality failure                5              6
conjunction graph failure                   5              6
conditional three-projection partition     11             12.   (FSG1)
```

Thus every nonlinear context in the entire machine family is compiled by one
of three fixed class-two two-groups.  For the largest gate there are six
selector signs plus `J` and 24 noncentral generators, so the raw packet group
has order `2^31`; its simple dimensions are `2^11` on an allowed atom and
`2^12` on a violating atom.  These constants are large but independent of
machine input, computation depth, and matrix microstate dimension.

The MSI audit exhausted all `3!`, `3!`, and `6!` variable orders respectively
and checked every Boolean assignment by exact Gaussian elimination over
`F_2`.  The best orders have BDD baselines `5,5,11`.  By comparison, the
internally disjoint satisfying-path construction has baselines `6,10,102`.
The last reduction is therefore not cosmetic: it replaces a 103-dimensional
rank matrix by a 12-dimensional one.

This closes packet-size growth for the actual Fanizza system.
`every-forbidden-atom-has-fixed-schur-pauli-words` also names the extra pair
after cutting to each of the finitely many forbidden atoms.  Installing its
three endpoint-sharing transports remains the local presentation theorem.
