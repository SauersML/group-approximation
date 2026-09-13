---
rg: 2
id: asymptotically-cat0-groups-rips-proof
kind: route
title: The orbit Rips complex of a torsion-free asymptotically CAT(0) group is a Cayley flag complex
target: torsion-free-asymptotically-cat0-groups-have-contractible-rips
requires:
  - asymptotically-cat0-orbits-have-contractible-rips-complexes
  - group-rips-complexes-are-cayley-graph-flag-complexes
---

By the first required claim, `VR_t(X)` is contractible for some `t`, where
`X = G.x_0` carries the induced metric `d`.

The action is properly discontinuous, so the stabilizer of `x_0` is finite, hence
trivial since `G` is torsion-free. So `g ↦ g x_0` is a bijection `G → X`, and it carries
`VR_t(X)` isomorphically onto the complex on `G` whose simplices are the finite sets with
`d(g x_0, h x_0) ≤ t` pairwise. As `d(g x_0, h x_0) = d(x_0, g^{-1} h x_0)`, this is the
clique complex of `Cay(G, T)` with `T = {g ≠ 1 : d(x_0, g x_0) ≤ t}`.

`T` is finite since only finitely many `g` move the compact ball `B(x_0, t)` to meet
itself, and symmetric. It generates `G`: the Cayley graph `Cay(G, T)` is the 1-skeleton of
the contractible, hence connected, complex. By
`group-rips-complexes-are-cayley-graph-flag-complexes` (item 1), the clique complex of
`Cay(G, T)` is the Rips complex `R_1(G, T)` of the word metric `d_T`. ∎
