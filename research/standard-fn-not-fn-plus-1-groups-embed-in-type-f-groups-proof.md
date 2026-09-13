---
rg: 2
id: standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups-proof
kind: route
title: "Classical F_n-not-F_{n+1} groups have F_infinity hosts: containment by construction plus cited finiteness of the hosts"
target: standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups
requires: []
---

Direct proof. Each containment holds by definition, and each host's finiteness
type is a cited theorem.

1. `SB_n <= F^{(1)} x ... x F^{(n)}`, since `SB_n` is a kernel inside that
   product. A finite product of finitely generated free groups has a finite
   `K(π,1)`, so it is of type `F`, hence of type `F_∞`.

2. `BB_L <= A_L`, since `BB_L = ker(A_L -> Z)`. The Salvetti complex of `A_L`
   is a finite `K(π,1)` (Charney--Davis), so `A_L` is of type `F`, hence of type
   `F_∞`.

3. `A_n(Z[1/p]) <= GL_n(Z[1/p])`, since Abels' group is a matrix group.
   `GL_n(Z[1/p])` is S-arithmetic in characteristic zero, so it is of type
   `F_∞` (Borel--Serre 1976). It has torsion, so this host is of type `F_∞` and
   not of type `F`.

The finiteness types of the small groups (Bieri 1976, Stallings 1963,
Bestvina--Brady 1997, Abels--Brown 1987) only show that the families realise
the gap. The conclusion that they have `F_∞` hosts does not depend on them.
This route imports the host finiteness statements; it does not reprove them.
