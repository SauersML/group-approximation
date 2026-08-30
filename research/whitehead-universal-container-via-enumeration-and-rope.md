---
rg: 2
id: whitehead-universal-container-via-enumeration-and-rope
kind: route
title: Free-product all recursive presentations, compress once, and apply the rope once
target: whitehead-universal-finitely-presented-container
requires: [whitehead-injective-two-generator-recursive-compression, whitehead-injective-torsion-order-preserving-higman-embedding]
---

Effectively enumerate every countably generated recursively enumerable
presentation code

```text
P_i=<x_(i,1),x_(i,2),... | R_i>,  i>=1.
```

This enumerates syntax, not semantic group properties: dovetail all Turing
machines enumerating relators on tagged recursive alphabets. Form the single
countably generated recursively presented group

```text
Q=*_(i>=1) P_i.
```

Every countably generated recursively presented group `K` is isomorphic to
some factor `P_i`. The factor inclusion `P_i->Q` is split by the
retraction killing all other factors, so its map on Whitehead groups is split
injective.

Apply
[[whitehead-injective-two-generator-recursive-compression]] once to obtain a
two-generator recursively presented group `E` with `Q->E` an embedding,
`Wh(Q)->Wh(E)` injective, and `Tord(E)=Tord(Q)`. Then apply
[[whitehead-injective-torsion-order-preserving-higman-embedding]] once to
this single `E`. It gives a finitely presented `U` with `E->U` an
embedding, `Wh(E)->Wh(U)` injective, and `Tord(U)=Tord(E)`.

The group `U` is selected after the fixed groups `Q,E` and before any
input `K`. For a chosen presentation index of `K`, compose

```text
K ~= P_i -> Q -> E -> U.
```

Every arrow is an embedding and the induced Whitehead map is injective.
Since the enumeration includes `C_n` for every `n>=2`,
`Tord(Q)={2,3,4,...}`, and exact torsion preservation gives the same
spectrum for `U`.

Finally `Wh(C_5)` is nonzero (indeed isomorphic to `Z`), so its injective
image proves `Wh(U)` is nonzero. QED
