---
rg: 2
id: a-theory-fj-fixed-two-generator-all-group-tester
kind: claim
title: One two-generator finitely presented group tests A-theoretic Farrell--Jones for every group
distinct_from:
  a-theory-fj-fixed-two-generator-tester: that uses a torsion-free host and quantifies only over torsion-free groups; this is the unrestricted all-group reduction.
  full-farrell-jones-fixed-two-generator-all-group-tester: that concerns algebraic K- and L-theory; this concerns nonconnective Waldhausen A-theory.
  universal-all-group-subgroup-colimit-class-tester: that is property-independent; this is its A-theoretic Farrell--Jones instance.
---

Let `FJ_A` be the class of groups satisfying Farrell--Jones for
nonconnective Waldhausen A-theory with coefficients and finite wreath
products.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
U belongs to FJ_A
  <=>
every group belongs to FJ_A.
~~~

The same torsionful all-group host `U` from
[[universal-all-group-subgroup-colimit-class-tester]] works, and
`Tord(U)={2,3,4,...}`. This is an exact reduction only.

**ESTABLISHED 2026-08-31** by
[[a-theory-fj-all-group-tester-proof]].
