---
rg: 2
id: f3-hosts-for-fp-groups-via-double-edge-splitting
kind: route
title: "Dead: an F_3 host of a universal group that splits over a double with vertex groups of finite rational H_2"
target: every-finitely-presented-group-embeds-in-an-f3-group
requires: []
---

**Dead route**, recorded so the attempt stays visible. It is killed by
`fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3` through that claim's
`invalidates:`.

The attempt: realize a universal finitely presented group `U` inside the
fundamental group of a finite graph of groups with two properties, and show
the result is of type `F_3`.
- Every vertex group has finite-dimensional rational `H_2`, for instance is
  of type `FP_2(Q)`.
- Some edge group is a double `F_1 *_R F_2` of a presentation `F/R` of an
  infinite group with `R ≠ 1`, which is how relations are imposed in Higman's
  rope trick.

Why it dies: such a double has infinite-dimensional `H_2(-; Q)`
(Fournier-Facio–Zaremsky arXiv:2607.21727v1, Lemma 3.3). A finite graph of
groups with finite rational `H_2` at every vertex and infinite rational `H_2`
at some edge has infinite-dimensional `H_3(-; Q)`, so it is not of type
`FP_3(Q)` and in particular not of type `F_3`.
