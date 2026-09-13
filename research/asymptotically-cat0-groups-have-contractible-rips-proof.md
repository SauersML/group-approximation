---
rg: 2
id: asymptotically-cat0-groups-have-contractible-rips-proof
kind: route
title: Zaremsky's contractible orbit Vietoris–Rips complex plus twin collapse gives a contractible Cayley flag complex
target: asymptotically-cat0-groups-have-contractible-rips
requires:
  - asymptotically-cat0-orbits-have-contractible-rips-complexes
  - flag-complex-proper-vertex-transitive-action-rips
---

Let `X = G x_0` with the metric `d` induced from `𝔛`. By the first prerequisite,
`VR_t(X)` is contractible for some `t`.

1. `VR_t(X)` is a flag simplicial complex, since its simplices are the finite sets
   whose points are pairwise within `t`.
2. It is locally finite: by proper discontinuity only finitely many `g` move the
   compact ball `B(x_0, t)` to meet itself, so only finitely many orbit points lie
   within `t` of `x_0`, and likewise for every orbit point.
3. `G` acts on `X` by isometries, so it acts simplicially on `VR_t(X)`. The action is
   transitive on the vertex set `X`, and the vertex stabilizers are finite by proper
   discontinuity.
4. Apply `flag-complex-proper-vertex-transitive-action-rips` with `v = x_0`. Two
   distinct orbit points are adjacent iff they are within `t`, so the generating set
   it produces is `{g ≠ 1 : g x_0 = x_0 or d(g x_0, x_0) <= t} = S_t`. Hence
   `P_1(G, S_t) ≃ VR_t(X)` is contractible.
