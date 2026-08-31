---
rg: 2
id: bost-all-group-tester-proof
kind: route
title: Check every subgroup of every finite-presentation stage
target: bost-fixed-two-generator-all-group-tester
requires:
  - whitehead-universal-finitely-presented-container
  - bost-fixed-two-generator-torsion-free-tester
---

Fix the all-group universal host `U` from
[[whitehead-universal-finitely-presented-container]] and assume `Bost(U)`.
Let `G` be an arbitrary discrete group and write it as a directed colimit

~~~text
G=colim_i P_i
~~~

of finitely presented groups. Every `P_i` embeds in `U`.

Bartels--Echterhoff--Lueck, *Inheritance of isomorphism conjectures under
colimits*, EMS Series of Congress Reports (2008), 41--70,
DOI 10.4171/060-1/2, Theorem 0.7(i), explicitly permits noninjective
structure maps. Its Bost hypothesis asks for the assembly conjecture on
every subgroup of every stage, rather than merely on each stage.

That stronger hypothesis follows from `Bost(U)`. If `H<=P_i`, compose with
`P_i->U`. The group `U` is countable discrete and `H` is an open subgroup.
Paravicini, *The Bost conjecture, open subgroups and groups acting on
trees*, J. K-Theory 4 (2009), 469--490, arXiv:0902.4339, Theorem 3.7 and
Corollary 3.8, passes Bost with arbitrary separable coefficients from `U`
to `H`. Hence Theorem 0.7(i) gives `Bost(G)`.

Conversely, the universal assertion applies to the particular group `U`.
This proves the exact equivalence even for uncountable colimits, without
asserting a subgroup-permanence theorem outside the countable discrete
setting in which it is used.

The arbitrary-map distinction is essential: Theorem 0.7(ii) gives only the
injective-system statement for reduced Baum--Connes, so no Baum--Connes
tester is inferred here. QED
