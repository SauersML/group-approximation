---
rg: 2
id: coarsely-injective-groups-with-torsion-have-contractible-rips
kind: claim
title: Every group acting properly and coboundedly on a coarsely injective space has a contractible Rips complex, torsion allowed
distinct_from:
  coarsely-injective-groups-have-contractible-rips-complexes: that is the torsion-free case, where the orbit map is a bijection and the criterion is run on G itself; this runs the criterion on the orbit set, with finite point stabilizers, and collapses twin vertices, which is needed for mapping class groups and other hierarchically hyperbolic groups with torsion
  asymptotically-cat0-groups-have-contractible-rips: that is the same twin-collapse extension for asymptotically CAT(0) spaces; this is the l-infinity-type case of coarsely injective spaces, which covers groups that are not CAT(0)
  helly-groups-have-contractible-rips-complexes: that is a nerve-theorem proof for groups acting on Helly graphs; this covers every coarsely injective group, including hierarchically hyperbolic groups not known to be Helly
---

**ESTABLISHED** (route `coarsely-injective-groups-with-torsion-rips-proof`).

Let `(E, d)` be `δ`-coarsely injective: for every family of closed balls `B(x_i, r_i)` with
`d(x_i, x_j) ≤ r_i + r_j` for all `i, j`, there is a point within `r_i + δ` of every `x_i`.
Let a group `G` act on `E` by isometries, properly (for each ball `B`, only finitely many
`g` have `gB ∩ B ≠ ∅`) and coboundedly: for some `x_0 ∈ E` and `D ≥ 0`, every point of `E`
lies within `D` of `G x_0`. No torsion-freeness is assumed.

Then for every integer `t ≥ t_0 := ⌈4δ + 4D + 2⌉`, the set
`T_t = {g ∈ G ∖ {1} : d(x_0, g x_0) ≤ t}` is a finite symmetric generating set of `G`, and
the Rips complex `P_1(G, T_t)`, the clique complex of `Cay(G, T_t)`, is contractible.

Consequences:

- `hierarchically-hyperbolic-groups-have-contractible-rips`: every hierarchically
  hyperbolic group, for example every mapping class group of a surface, torsion included;
- `closed-3-manifold-hhg-groups-have-contractible-rips-complexes`;
- with `contractible-rips-conjugates-p-subgroups-into-balls`, every finite `p`-subgroup of
  such a group is conjugate into the finite set `T_t ∪ {1}`.

What is new compared with `coarsely-injective-groups-have-contractible-rips-complexes` is
only Step 0 of the route: the metric lives on the orbit, not on `G`, and the finite
stabilizer of `x_0` is absorbed by `flag-complex-proper-vertex-transitive-action-rips`.
