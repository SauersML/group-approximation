---
rg: 2
id: bvc-counterexample-from-fp-torsion-free-few-class-group
kind: route
title: "An infinite finitely presented torsion-free group with finitely many conjugacy classes refutes Conjecture B"
target: some-fp-non-vc-group-has-property-bvc
requires: [some-infinite-fp-torsion-free-group-has-finitely-many-classes]
---

Let `G` be infinite, torsion-free, finitely presented, with conjugacy class
representatives `1, g_1, ..., g_k`.

- **BVC.**  The virtually cyclic subgroups of a torsion-free group are the
  trivial group and the infinite cyclic subgroups (von Puttkamer--Wu,
  arXiv:1607.03790v2, Lemma 1.4 and the sentence after it).  Any `<h>` with
  `h != 1` has `h` conjugate to some `g_i`, so `<h>` is conjugate to `<g_i>`.
  Hence `<g_1>, ..., <g_k>` witness BVC.
- **Not virtually cyclic.**  An infinite torsion-free virtually cyclic group
  is infinite cyclic, and `Z` has infinitely many conjugacy classes.

So `G` witnesses `some-fp-non-vc-group-has-property-bvc`.  `∎`

The prerequisite is strictly stronger than the target.  The route records
that Conjecture B already rules out one famous unknown object: an infinite
finitely presented torsion-free group with finitely many conjugacy classes.
