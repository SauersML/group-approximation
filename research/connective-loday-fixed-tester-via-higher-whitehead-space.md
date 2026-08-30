---
rg: 2
id: connective-loday-fixed-tester-via-higher-whitehead-space
kind: route
title: Detect connective assembly by the whole Whitehead space
target: connective-loday-assembly-fixed-fp-torsion-free-tester
requires: [higher-whitehead-universal-finitely-presented-torsion-free-group, torsion-free-directed-colimit-recursively-presented]
---

Waldhausen, Corollary 15.5, identifies `K(NG;Z)` with the homotopy fibre
of

```text
K(ZG) -> Wh_Z(G).
```

Thus the connective assembly is a weak equivalence exactly when
`Wh_Z(G)` is weakly contractible. Assertion 15.9 identifies this assembly
with Loday's map on all connective homotopy groups.

Choose `U` from
[[higher-whitehead-universal-finitely-presented-torsion-free-group]] and
suppose its connective assembly is a weak equivalence. Then
`Wh_i(U)=0` for every `i>=0`. If `K` is countably generated,
recursively presented, and torsion-free, the universal embedding injects
every `Wh_i(K)` into `Wh_i(U)`. Hence every `Wh_i(K)` vanishes and
`Wh_Z(K)` is weakly contractible.

For arbitrary torsion-free `G`, write

```text
G=colim_j K_j
```

using [[torsion-free-directed-colimit-recursively-presented]]. Waldhausen
states in the proof of Theorem 19.4 that `Wh_R(-)` commutes with filtering
direct limits. Therefore

```text
Wh_i(G)=colim_j Wh_i(K_j)=0
```

for every `i>=0`. These Whitehead spaces have CW homotopy type, so
`Wh_Z(G)` is weakly contractible and the connective assembly for `G` is
a weak equivalence.

The converse applies the universal assertion to the torsion-free group
`U`.

Source: Friedhelm Waldhausen, *Algebraic K-theory of generalized free
products, Part 2*, Ann. of Math. (2) 108 (1978), 205--256:
Proposition 15.3, Definition 15.4, Corollary 15.5, Definition 15.6,
Assertion 15.9, Remark 3 after Corollary 17.2.3, and the direct-limit
statement in the proof of Theorem 19.4. QED

This does not show that `K_n(ZK)->K_n(ZU)` is injective. Nor does an
isomorphism of one isolated component `A_n^U` suffice: the long exact
Whitehead sequence involves adjacent obstruction groups.
