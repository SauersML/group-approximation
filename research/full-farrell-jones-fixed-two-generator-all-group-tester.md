---
rg: 2
id: full-farrell-jones-fixed-two-generator-all-group-tester
kind: claim
title: One two-generator finitely presented group tests Full Farrell--Jones for every group
distinct_from:
  full-farrell-jones-fixed-fp-torsion-free-tester: that uses a torsion-free host and quantifies only over torsion-free groups; this uses the all-group host and tests the conjecture including groups with torsion.
  luck-determinant-fixed-two-generator-tester: that tests one analytic consequence over integral group rings; this tests the coefficient-rich algebraic K- and L-theoretic Farrell--Jones package.
  universal-all-group-subgroup-colimit-class-tester: that is the abstract mechanism; this verifies its hypotheses for Full Farrell--Jones.
---

Let `FJ` denote Lueck's Full Farrell--Jones class: algebraic K- and L-theory
with additive-category coefficients and finite wreath products.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
U belongs to FJ
  <=>
every group belongs to FJ.
~~~

The group `U` is the torsionful host in
[[universal-all-group-subgroup-colimit-class-tester]], with
`Tord(U)={2,3,4,...}`. The quantifier on the right includes all torsion
groups. This is an exact reduction, not a proof of Full Farrell--Jones for
`U` or for all groups.

**ESTABLISHED 2026-08-31** by
[[full-farrell-jones-all-group-tester-proof]].
