---
rg: 2
id: a-theory-fj-all-group-tester-proof
kind: route
title: Apply A-theoretic Farrell--Jones inheritance without a torsion restriction
target: a-theory-fj-fixed-two-generator-all-group-tester
requires:
  - universal-all-group-subgroup-colimit-class-tester
  - a-theory-fj-two-generator-tester-proof
---

Enkelmann--Lueck--Pieper--Ullmann--Winges, *On the Farrell--Jones
conjecture for Waldhausen's A-theory*, Geom. Topol. 22 (2018),
3321--3394, DOI 10.2140/gt.2018.22.3321, Theorem 1.1(ii), proves that
`FJ_A` passes to arbitrary subgroups and to directed colimits whose
structure maps need not be injective.

Thus `FJ_A` satisfies both hypotheses of
[[universal-all-group-subgroup-colimit-class-tester]]. Applying that theorem
to its fixed two-generator finitely presented all-group host `U` gives

~~~text
U in FJ_A  <=>  every group is in FJ_A.
~~~

The earlier route [[a-theory-fj-two-generator-tester-proof]] uses the same
permanence theorem in the torsion-free lane; the present application removes
that restriction by using the torsionful all-group host. QED
