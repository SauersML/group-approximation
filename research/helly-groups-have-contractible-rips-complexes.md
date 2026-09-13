---
rg: 2
id: helly-groups-have-contractible-rips-complexes
kind: claim
title: Every Helly group has a Cayley graph with contractible clique complex, at every even orbit scale
distinct_from:
  coarsely-injective-groups-have-contractible-rips-complexes: that derives contractibility for torsion-free coarsely injective groups from Zaremsky's small-ball criterion; this is an independent nerve-theorem proof for Helly graphs that allows torsion and gives explicit scales
  every-type-f-group-has-a-contractible-rips-complex: that is the universal affirmative answer to Problem 4.7; this proves the property for Helly groups only
  amenable-automatic-groups-have-contractible-rips-complexes: that is the open claim of Problem 4.1 for amenable automatic groups; this is an established claim for groups acting geometrically on Helly graphs
---

Let `G` act on a connected locally finite Helly graph `X` with finite vertex stabilizers
and finitely many vertex orbits. Fix a vertex `x_0` and put
`D = max_v d(v, G x_0)`. For every integer `s ≥ D + 1`, the set
`T_s = {g ≠ 1 : d(x_0, g x_0) ≤ 2s}` is a finite symmetric generating set and the clique
complex of `Cay(G, T_s)`, which is the Rips complex `R_1(G, T_s)`, is contractible. If some
Cayley graph `Cay(G, T)` is itself Helly, then `(G, T)` is of type R: `R_r(G, T)` is
contractible for all `r ≥ 1`.

Examples (Chalopin–Chepoi–Genevois–Hirai–Osajda, arXiv:2002.06895v3, Theorems 1.1 and 1.3,
and p. 4): hyperbolic groups, CAT(0) cubical groups, finitely presented graphical
C(4)–T(4) small cancellation groups, type-preserving uniform lattices in buildings of type
`C_n`, graph products, free products and HNN extensions over finite subgroups, FC-type
Artin groups and weak Garside groups of finite type (e.g. braid groups). The torsion-free
ones are of type F.

Proof: route `helly-groups-have-contractible-rips-complexes-proof`, full argument in
`research/artifacts/zp-helly-groups-contractible-rips-2026-09-13.md`. Unreviewed.
