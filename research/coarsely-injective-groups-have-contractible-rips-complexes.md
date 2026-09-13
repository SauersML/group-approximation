---
rg: 2
id: coarsely-injective-groups-have-contractible-rips-complexes
kind: claim
title: A torsion-free group acting properly and coboundedly on a coarsely injective space has a contractible Rips complex
distinct_from:
  torsion-free-asymptotically-cat0-groups-have-contractible-rips: that covers groups acting on asymptotically CAT(0) spaces through Euclidean-type link criteria; this covers l-infinity-type geometry (Helly graphs, injective spaces, hierarchically hyperbolic groups), where those criteria fail
  every-type-f-group-has-a-contractible-rips-complex: that is the universal affirmative answer to Problem 4.7; this proves the property for torsion-free coarsely injective groups only
  amenable-automatic-groups-have-contractible-rips-complexes: that is the open claim of Problem 4.1 for amenable automatic groups; this is an established claim for torsion-free groups acting on coarsely injective spaces
---

Let `(E, d)` be `δ`-coarsely injective: for every family of closed balls `B(x_i, r_i)` with
`d(x_i, x_j) ≤ r_i + r_j` for all `i, j`, there is a point within `r_i + δ` of every `x_i`.
Let `G` be torsion-free and act on `E` by isometries, properly (for each ball `B`, only
finitely many `g` have `gB ∩ B ≠ ∅`) and coboundedly: every point of `E` lies within `D` of
`G x_0`.

Then for every integer `t > t_0 := ⌈4δ + 4D + 2⌉`, the set
`T_t = {g ≠ 1 : d(x_0, g x_0) ≤ t}` is a finite symmetric generating set of `G`, and the
Rips complex `R_1(G, T_t)`, the clique complex of `Cay(G, T_t)`, is contractible. So
Problem 4.7 has a positive answer for these groups in the reading "some finite generating
set, some scale".

Coverage: Helly groups (Chalopin–Chepoi–Genevois–Hirai–Osajda), including hyperbolic,
CAT(0) cubical, C(4)–T(4), FC-type Artin and weak Garside groups; and hierarchically
hyperbolic groups (`torsion-free-hhg-subgroups-have-contractible-rips-complexes`).

Proof: route `coarsely-injective-groups-rips-proof`. Unreviewed.
