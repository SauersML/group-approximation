---
rg: 2
id: bost-fixed-two-generator-torsion-free-tester-proof
kind: route
title: Combine open-subgroup inheritance with arbitrary Bost colimits
target: bost-fixed-two-generator-torsion-free-tester
requires:
  - two-generator-fp-torsion-free-master-tester
  - torsion-free-directed-colimit-recursively-presented
---

Let `E` be the group from
[[two-generator-fp-torsion-free-master-tester]] and suppose `Bost(E)`.

Every subgroup of the countable discrete group `E` is open. Paravicini
proves that the Bost conjecture with arbitrary separable C-star-algebra
coefficients passes from a countable discrete group to every subgroup.
Therefore every subgroup of `E` satisfies Bost.

Now let `G` be an arbitrary torsion-free discrete group and write

```text
G = colim_i K_i
```

using [[torsion-free-directed-colimit-recursively-presented]]. Every `K_i`
embeds in `E`; hence every subgroup of every `K_i` satisfies Bost with
the relevant restricted coefficients.

Bartels--Echterhoff--Lueck, Theorem 0.7(i), applied to their assembly map
(0.4), now gives Bost with coefficients for `G`. Their theorem explicitly
allows noninjective structure maps. Its hypothesis quantifies over all
subgroups of the stages, which is why the preceding open-subgroup theorem
is used rather than an unsupported bare colimit assertion.

Conversely, if every torsion-free group satisfies Bost with coefficients,
then `E` does because `E` is torsion-free.

Sources:

- Walther Paravicini, *The Bost conjecture, open subgroups and groups acting
  on trees*, J. K-Theory 4 (2009), 469--490, arXiv:0902.4339,
  Theorem 3.7 and Corollary 3.8.
- Arthur Bartels, Siegfried Echterhoff, and Wolfgang Lueck,
  *Inheritance of isomorphism conjectures under colimits*, in
  *K-Theory and Noncommutative Geometry*, EMS Series of Congress Reports
  (2008), 41--70, doi:10.4171/060-1/2, Theorem 0.7(i).

The same Bartels--Echterhoff--Lueck theorem explicitly omits reduced
Baum--Connes assembly (their map (0.5)) from the arbitrary-map assertion;
only its injective-system version appears in Theorem 0.7(ii). QED
