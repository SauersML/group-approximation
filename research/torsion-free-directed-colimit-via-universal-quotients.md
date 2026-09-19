---
rg: 2
id: torsion-free-directed-colimit-via-universal-quotients
kind: route
title: Reflect finite presentation approximants into torsion-free groups
target: torsion-free-directed-colimit-recursively-presented
requires: [torsion-free-universal-quotient-recursively-presented]
---

Let `G` be torsion-free. Choose a surjection

```text
F(X) -> G
```

from a free group on an arbitrary set `X`, and let `N` be its kernel.

Let `I` be the directed poset of pairs `(X_0,R_0)` where `X_0` is a
finite subset of `X` and `R_0` is a finite subset of
`N intersect F(X_0)`. Order the pairs by inclusion in both coordinates
and put

```text
P_i = <X_0 | R_0>.
```

The inclusions give a directed system with colimit `G`: every generator
occurs at a stage, and every word in `N` has finite support and is inserted
as a relator at a later stage.

Write

```text
q_i:P_i -> T_i:=P_i^tf
```

for the universal torsion-free quotient. Its universal property makes the
abstract quotient functorial. If `f_ij:P_i->P_j` is a structure map, then
`q_j f_ij` has torsion-free target, so it factors uniquely through
`T_i->T_j`. Uniqueness proves the identity and composition laws. Chiodo,
Corollary 3.4 and Proposition 3.8, show that every `T_i` is torsion-free
and recursively presented on the same finite generating set as `P_i`.

Set `C=colim_i T_i`. Naturality of the quotients gives

```text
q:G=colim_i P_i -> C.
```

Since `G` is torsion-free, every canonical map `a_i:P_i->G` factors
uniquely as `P_i ->^q_i T_i ->^b_i G`. The compatible `b_i` induce
`b:C->G`. On every `P_i`, the composite `bq` agrees with `a_i`, so
`bq=id_G`.

Conversely, if `c_i:T_i->C` is the colimit map, then

```text
q b c_i q_i = q a_i = c_i q_i.
```

Every `q_i` is surjective, hence `qbc_i=c_i`; the colimit maps are jointly
epimorphic, so `qb=id_C`. Therefore `C` is canonically isomorphic to
`G`.

Source: Maurice Chiodo, *On torsion in finitely presented groups*, Groups
Complexity Cryptology 6 (2014), 1--8, Corollary 3.4 and Proposition 3.8,
DOI 10.1515/gcc-2014-0001. QED
