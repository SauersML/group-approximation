---
rg: 2
id: fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3
kind: claim
title: "A finite graph of groups with finite rational H_2 at every vertex and infinite rational H_2 at some edge has infinite rational H_3"
invalidates:
  - f3-hosts-for-fp-groups-via-double-edge-splitting
---

Let `K` be the fundamental group of a finite graph of groups, with finitely
many vertex groups `G_v` and edge groups `G_e`. Suppose:

- `dim_Q H_2(G_v; Q) < ∞` for every vertex `v`;
- `dim_Q H_2(G_e; Q) = ∞` for some edge `e`.

Then `dim_Q H_3(K; Q) = ∞`. In particular `K` is not of type `FP_3(Q)`, so it
is not of type `FP_3`, `F_3` or `F_∞`.

**Use for Problem 1.1.** Take any container of a group that splits as a
finite graph of groups whose vertex groups have finite rational `H_2`, for
instance vertex groups of type `FP_2(Q)`. It can be of type `FP_3(Q)` only if
every edge group has finite-dimensional rational `H_2`. The double
`L = F *_R F` of a free group of finite rank along a normal subgroup `R` of
infinite rank has infinite-dimensional `H_2(L; Q)` (Fournier-Facio–Zaremsky,
arXiv:2607.21727v1, Lemma 3.3). So no such container can use a double as an
edge group, whatever the edge maps are. This kills the route
`f3-hosts-for-fp-groups-via-double-edge-splitting`. Higman's rope trick uses
the double as its edge group. There the vertex group is `P × G`, which has
infinite rational `H_2` when `G` does, and that case is handled separately by
`twisted-rope-trick-container-is-not-fp3-over-fp2-hosts` and by Theorem B
(`higman-rope-trick-group-is-never-fp3`).

The obstruction is different from the converse half of Bieri's Proposition
2.13, which needs edge groups of type `FP_n` to force vertex groups of type
`FP_n`. Here the edge groups are the ones that are too large.
