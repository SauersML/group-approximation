---
rg: 2
id: f-infinity-finite-cd-groups-type-f-via-universal-tester
kind: route
title: "Vanishing of K~_0 for the one universal finitely presented torsion-free tester answers Problem 1.21 positively"
target: f-infinity-groups-of-finite-cd-are-of-type-f
requires: [reduced-k0-of-universal-fp-torsion-free-tester-vanishes, higher-whitehead-universal-finitely-presented-torsion-free-group, f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f]
---

Assume `K̃_0(Z[U]) = 0` for the fixed finitely presented torsion-free group `U`
([[reduced-k0-of-universal-fp-torsion-free-tester-vanishes]]). Let `G` be of
type `F_∞` with `cd G < ∞`.

`G` is finitely presented, since `F_∞` implies `F_2`. So it is finitely
generated and recursively presented. It is torsion-free because its
cohomological dimension is finite (see
[[f-infinity-finite-cd-groups-type-f-via-hsiang]]).

By [[higher-whitehead-universal-finitely-presented-torsion-free-group]], there
is an embedding `G → U` with `Wh_0(G) → Wh_0(U)` injective. `Wh_0(H)` is
`π_0` of the cofibre of Waldhausen's assembly `h(BH; K(Z)) → K(Z[H])`. On
`π_0` the assembly is `K_0(Z) = Z → K_0(Z[H])`, and `π_{−1}` of the connective
homology vanishes. So `Wh_0(H) = K̃_0(Z[H])`, as that node records.

Hence `K̃_0(Z[G])` injects into `K̃_0(Z[U]) = 0`. So `K̃_0(Z[G]) = 0`, and
[[f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f]] makes `G` of
type F. QED

Contrapositive: a negative answer to Problem 1.21 produces a nonzero element
of `K̃_0(Z[U])` for this one fixed finitely presented group. Unlike
[[f-infinity-finite-cd-groups-type-f-via-hsiang]], this route needs no
directed-colimit argument.
