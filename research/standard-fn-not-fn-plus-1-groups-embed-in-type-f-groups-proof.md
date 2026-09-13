---
rg: 2
id: standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups-proof
kind: route
title: "Standard F_n-not-F_{n+1} groups embed in type-F groups: definitional containment plus cited finiteness of the overgroups"
target: standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups
requires: []
---

Direct proof. Each named containment is definitional and each overgroup's
finiteness type is a cited theorem:

1. `SB_n <= F^{(1)} x ... x F^{(n)}` by definition (`SB_n` is a kernel inside
   that product). A direct product of finitely many finitely generated free
   groups has a finite `K(pi,1)` (a product of finite wedges of circles), so
   it is of type `F`. Finiteness type of `SB_n`: Bieri 1976, Stallings 1963.

2. `BB_L <= A_L` by definition (`BB_L = ker(A_L -> Z)`). The RAAG `A_L` has
   the finite Salvetti complex as a `K(pi,1)`, so it is of type `F`
   (Charney--Davis; Bestvina--Brady 1997). Finiteness type of `BB_L`:
   Bestvina--Brady 1997, Main Theorem.

3. `A_n(Z[1/p]) <= GL_n(Z[1/p])` by definition (Abels' group is a matrix
   group). `GL_n(Z[1/p])` is S-arithmetic in characteristic zero, hence of
   type `F_infinity`. Finiteness type of `A_n(Z[1/p])`: Abels 1987,
   Abels--Brown 1987.

In every case the finiteness type of the small group and the type-`F`
(or type-`F_infinity`) property of the overgroup are recorded facts, and the
embedding is by construction; the conjunction is the claim. This route asserts
the containments and cites the finiteness statements from the sources; it does
not reprove them.
