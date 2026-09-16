---
rg: 2
id: cantor-configuration-function-modules-are-v-acyclic
kind: claim
title: For every m >= 1 the V-module of compactly supported integer functions on the configuration space of m distinct Cantor points is V-acyclic
distinct_from:
  cantor-power-function-modules-are-v-acyclic: that claim is about C(C^j, Z) on the full power C^j; this is C_c on the open configuration space, and implies that one by induction over the fat diagonal
artifacts:
  - research/artifacts/cantor-configuration-modules-v-acyclic-germ-groupoid-2026-09-16.md
---

Let `C = {0,1}^N` be the Cantor set and let Thompson's group `V` act diagonally on
`C^m`. `Conf_m(C) ⊆ C^m` is the open set of `m`-tuples of pairwise distinct points.
`C_c(Conf_m(C), Z)` is the group of compactly supported locally constant integer
functions on it, with `V` acting by translation.

The claim: `H_p(V; C_c(Conf_m(C), Z)) = 0` for all `p >= 0` and all `m >= 1`.

For `m = 1` this is `H_p(V; C(C, Z)) = 0`. Rationally it is Lemma C5 of
`research/artifacts/zp-braided-v-rational-acyclicity-2026-09-13-part3.md`.

Route: `cantor-configuration-modules-v-acyclic-germ-proof`, a germ groupoid comparison
through the Crainic–Moerdijk Leray spectral sequence.
