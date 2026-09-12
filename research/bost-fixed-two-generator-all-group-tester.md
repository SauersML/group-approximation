---
rg: 2
id: bost-fixed-two-generator-all-group-tester
kind: claim
title: One two-generator finitely presented group tests the Bost conjecture with coefficients for every group
distinct_from:
  luck-determinant-fixed-two-generator-tester: that tests Fuglede--Kadison determinant bounds for integral group-ring matrices; this tests the coefficient-sensitive Bost assembly map for L1 crossed products.
  bost-fixed-two-generator-torsion-free-tester: that uses a torsion-free host and tests only torsion-free groups; this tests all discrete groups with the torsionful universal host.
  full-farrell-jones-fixed-two-generator-all-group-tester: that concerns algebraic K- and L-theory over the virtually-cyclic family; this concerns topological K-theory of L1 crossed products over the finite-subgroup family.
  universal-all-group-subgroup-colimit-class-tester: that is the abstract tester; this checks the coefficient-sensitive Bost inheritance hypotheses.
---

Let `Bost(G)` mean the Bost conjecture with arbitrary separable
C-star-algebra coefficients in every degree.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
Bost(U)
  <=>
Bost(G) for every discrete group G.
~~~

The group `U` is the all-group host in
[[universal-all-group-subgroup-colimit-class-tester]] and has every finite
torsion order. This is an exact reduction only. It does not make the
corresponding assertion for reduced Baum--Connes, whose arbitrary-map
colimit permanence is unavailable.

**ESTABLISHED 2026-08-31** by
[[bost-all-group-tester-proof]].
