---
rg: 2
id: helly-groups-have-contractible-rips-complexes-proof
kind: route
title: Nerve of the orbit ball cover of a Helly clique complex is the orbit Rips complex
target: helly-groups-have-contractible-rips-complexes
requires: []
artifacts:
  - research/artifacts/zp-helly-groups-contractible-rips-2026-09-13.md
---

Direct proof; full details in the artifact.

1. **Ball intersections.** A nonempty finite intersection `W` of balls in the Helly graph
   `X` induces an isometric subgraph, and `Flag(X[W])` is contractible. Delete the vertices
   farthest from a base point one at a time; each is dominated by a closer vertex found by
   the Helly property, and deleting a dominated vertex from a flag complex is a homotopy
   equivalence.
2. **Whole complex.** `Flag(X)` is contractible (Whitehead; finite subcomplexes lie in balls).
   Powers `X^r` are Helly (CCGHO Lemma 5.28), so `Flag(X^r)` is contractible too.
3. **Cover.** For `s ≥ D + 1` the full subcomplexes `F_g = Flag(X[B(g x_0, s)])` cover
   `Flag(X)`. Finite intersections are `Flag` of ball intersections, contractible by 1.
   A finite set of `g`'s has nonempty intersection iff the balls pairwise meet, iff
   `d(g x_0, h x_0) ≤ 2s` pairwise. So the nerve is `VR_{2s}(G, ρ)`, with
   `ρ(g, h) = d(g x_0, h x_0)`.
4. **Nerve theorem** (Borsuk; Björner, Handbook of Combinatorics 1995, Theorem 10.6, quoted
   from memory): `VR_{2s}(G, ρ) ≃ Flag(X)`, which is contractible. `VR_{2s}(G, ρ)` is the
   clique complex of `Cay(G, T_s)`, and `T_s` generates because orbit points on a path
   are within `2D + 1 ≤ 2s` of each other.
5. **Helly Cayley graph.** If `X = Cay(G, T)`, then `R_r(G, T) = Flag(X^r)`, contractible by 2.

For torsion-free Helly groups the conclusion also follows from
`coarsely-injective-groups-have-contractible-rips-complexes`. That route uses Zaremsky's
criterion and does not need the nerve theorem quoted here.
