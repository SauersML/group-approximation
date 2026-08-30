---
rg: 2
id: degree-one-assembly-single-tester-proof
kind: route
title: Translate the universal Whitehead tester through the assembly cokernel
target: degree-one-assembly-single-fp-tester-equivalence
requires: [whitehead-universal-finitely-presented-torsion-free-group, whitehead-is-degree-one-assembly-cokernel]
---

Let `U` be the finitely presented torsion-free universal tester supplied by
[[whitehead-universal-finitely-presented-torsion-free-group]]. For every
group `H`, [[whitehead-is-degree-one-assembly-cokernel]] gives

```text
A_1^H is onto  <=>  Wh(H)=0.
```

The universal tester theorem gives

```text
Wh(U)=0  <=>  Wh(G)=0 for every torsion-free G.
```

Combining the two displayed equivalences, first for `H=U` and then for
all torsion-free `H=G`, proves the claim. QED
