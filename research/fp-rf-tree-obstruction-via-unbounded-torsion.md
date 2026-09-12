---
rg: 2
id: fp-rf-tree-obstruction-via-unbounded-torsion
kind: route
title: A finitely presented residually finite group with torsion of infinitely many prime orders fits in no regular rooted tree
target: some-fp-rf-group-acts-on-no-regular-rooted-tree
requires:
  - fp-rf-group-with-unbounded-prime-torsion
  - regular-tree-torsion-orders-have-primes-at-most-degree
---

Let `G` be the finitely presented residually finite group of
`fp-rf-group-with-unbounded-prime-torsion`. For each `d >= 2`, `G` has an
element of prime order `p > d`. So `G` does not embed in `Aut(T_d)`, by
`regular-tree-torsion-orders-have-primes-at-most-degree`. `∎`
