---
rg: 2
id: atlas-a4-19243-parabolic-subgroup-ladder-proof
kind: route
title: Exact F2 closure identifies the rank-three subgroup, its hyperplane stabilizer, and the final C3 escape
target: atlas-a4-19243-parabolic-subgroup-ladder
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-19243-s3xs3-localization
artifacts:
  - experiments/atlas_a4_19243_parabolic_ladder.py
---

The attached audit computes exact subgroups of `GL_4(F2)`.

First form

```text
H=<H_6,K>.
```

Closure gives `|H|=168`, and every matrix in `H` has both last row and last
column equal to `(0,0,0,1)`.  Therefore `H` lies in the standard block-diagonal
copy of `GL_3(F2)`.  That block-diagonal group has order

```text
|GL_3(F2)|=(8-1)(8-2)(8-4)=168,
```

so equality holds.

Next form `P=<H,b>`.  Exact closure gives `|P|=1344`.  Every element of `P`
fixes the last coordinate covector, while not every element fixes the last
basis vector.  The action of `GL_4(F2)` on its fifteen nonzero covectors is
transitive, so the stabilizer of one such covector has order

```text
20160/15=1344.
```

Hence `P` is the full hyperplane stabilizer.  In the usual block form it is

```text
F2^3 semidirect GL_3(F2) ~= AGL_3(F2).
```

Finally let `1 != z in Z(H_18)`.  Exact multiplication shows that neither
nontrivial central element lies in `P`, and closure of `<P,z>` has order
`20160`.  Since this is the order of `GL_4(F2)`, it is the whole group.

These three finite equalities prove `(A4-LADDER)`.  Together with the previous
localization, they also prove the structural statement: the syllables of
`q_19243` live before the final `C3` escape from the parabolic, while the large
packet component contains precisely that missing transverse direction.
