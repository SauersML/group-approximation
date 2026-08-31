---
rg: 2
id: bost-all-group-tester-proof
kind: route
title: Combine subgroup inheritance with the arbitrary-map Bost colimit theorem
target: bost-fixed-two-generator-all-group-tester
requires:
  - universal-all-group-subgroup-colimit-class-tester
  - bost-fixed-two-generator-torsion-free-tester-proof
---

Let `B` be the class of discrete groups satisfying the Bost conjecture with
arbitrary separable coefficients.

Paravicini, *The Bost conjecture, open subgroups and groups acting on
trees*, J. K-Theory 4 (2009), 469--490, arXiv:0902.4339, Theorem 3.7 and
Corollary 3.8, proves that Bost with coefficients passes from a countable
discrete group to every subgroup; all subgroups are open in the discrete
topology.

Bartels--Echterhoff--Lueck, *Inheritance of isomorphism conjectures under
colimits*, EMS Series of Congress Reports (2008), 41--70,
DOI 10.4171/060-1/2, Theorem 0.7(i), gives the Bost assembly statement for
a directed colimit with noninjective structure maps provided the relevant
assembly holds for all subgroups of the stages. If every stage lies in `B`,
Paravicini's subgroup theorem supplies exactly that hypothesis. Therefore
`B` is closed under arbitrary directed colimits as well as subgroups.

Apply [[universal-all-group-subgroup-colimit-class-tester]] to `B`. Its
fixed two-generator finitely presented host `U` satisfies

~~~text
Bost(U)  <=>  every group satisfies Bost.
~~~

The arbitrary-map distinction is essential: Theorem 0.7(ii) gives only the
injective-system statement for reduced Baum--Connes, so no Baum--Connes
tester is inferred here. QED
