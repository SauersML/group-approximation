---
rg: 2
id: full-farrell-jones-all-group-tester-proof
kind: route
title: Apply Full Farrell--Jones inheritance to the all-group host
target: full-farrell-jones-fixed-two-generator-all-group-tester
requires:
  - universal-all-group-subgroup-colimit-class-tester
  - full-farrell-jones-fixed-tester-via-subgroups-and-colimits
---

Wolfgang Lueck, *Survey on the Farrell--Jones Conjecture*, Bull. Amer.
Math. Soc. 63 (2026), 79--117, DOI 10.1090/bull/1876,
Theorem 8.12(ii)(a),(f), proves that the Full Farrell--Jones class is

1. inherited by arbitrary subgroups, and
2. closed under directed colimits with arbitrary, not necessarily
   injective, structure maps.

These are exactly the hypotheses of
[[universal-all-group-subgroup-colimit-class-tester]]. Applying that theorem
to the Full Farrell--Jones class and its fixed all-group host `U` gives the
claimed equivalence. This is the unrestricted version of the argument
recorded in [[full-farrell-jones-fixed-tester-via-subgroups-and-colimits]];
no torsion-free reflection is needed because `U` contains every finitely
presented group. Lueck's Remark 11.4 records this unrestricted universal
finitely presented group argument as well. QED
