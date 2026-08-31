---
rg: 2
id: two-generator-fp-all-group-master-tester
kind: claim
title: One two-generator finitely presented group tests major all-group approximation, ring, determinant, Bass, and dynamical conjectures
distinct_from:
  two-generator-fp-torsion-free-master-tester: that uses a torsion-free host and tests conjectures only on the torsion-free universe; this uses the torsionful universal host and quantifies over all groups.
  universal-local-approximation-fixed-two-generator-test-group: that records only finite-table approximation properties; this packages those with independent ring-theoretic, analytic, Bass, and cellular-automaton testers.
  universal-all-group-subgroup-colimit-class-tester: that is the abstract categorical mechanism; this records its named high-impact consumers together with consumers needing specialized finite-witness or Frattini arguments.
---

There exists one fixed two-generator finitely presented group `U`, with

~~~text
Tord(U)={2,3,4,...},
~~~

which simultaneously has all of the following exact tester properties.

1. For every class `C` closed under subgroups and arbitrary directed
   colimits, `U in C` iff every group belongs to `C`.
2. For every finite-table local approximation property `P_M`,
   `P_M(U)` iff every group has `P_M`; this includes soficity,
   hyperlinearity, operator-MF, LEF, weak soficity, and linear soficity.
3. `U` satisfies the integral classical Bass conjecture iff every group
   does.
4. `U` satisfies Lueck's determinant conjecture iff every group does.
5. `U` is surjunctive iff every group is surjunctive.
6. For every field `k`, `k[U]` is directly finite iff it is stably finite
   iff `k[G]` is directly finite for every group `G` iff `k[G]` is stably
   finite for every group `G`.

The same host works in every item; the quantifier is `exists U` before any
property, field, alphabet, or matrix is chosen. These are reductions, not
positive resolutions of the remaining open fixed-host assertions.

**ESTABLISHED 2026-08-31** by
[[two-generator-all-group-master-tester-inventory]].
