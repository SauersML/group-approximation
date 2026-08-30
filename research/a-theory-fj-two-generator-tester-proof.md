---
rg: 2
id: a-theory-fj-two-generator-tester-proof
kind: route
title: Apply A-theoretic Farrell--Jones inheritance to the universal tester
target: a-theory-fj-fixed-two-generator-tester
requires:
  - two-generator-fp-torsion-free-master-tester
---

Enkelmann--Lueck--Pieper--Ullmann--Winges define `FJ_A` using
nonconnective Waldhausen A-theory with coefficients and finite wreath
products. Their Theorem 1.1(ii) proves both permanence properties needed
here:

1. `FJ_A` passes to arbitrary subgroups;
2. `FJ_A` is closed under directed colimits whose structure maps need not
   be injective.

Apply item 6 of
[[two-generator-fp-torsion-free-master-tester]] to the class `C=FJ_A`.
It supplies the same two-generator finitely presented torsion-free nonsofic
non-MF group `E` and gives immediately

```text
E in FJ_A
  <=>
every torsion-free group is in FJ_A.
```

Source: Nils-Edvin Enkelmann, Wolfgang Lueck, Malte Pieper, Mark Ullmann,
and Christoph Winges, *On the Farrell--Jones conjecture for Waldhausen's
A-theory*, Geom. Topol. 22 (2018), 3321--3394,
doi:10.2140/gt.2018.22.3321, Conjecture 2.15 and Theorem 1.1(ii). QED
