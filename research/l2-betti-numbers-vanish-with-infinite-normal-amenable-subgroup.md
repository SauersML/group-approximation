---
rg: 2
id: l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup
kind: claim
title: A group with an infinite normal amenable subgroup has every L²-Betti number zero
distinct_from:
  l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers: that transfers vanishing from simplex stabilizers of an action on an acyclic complex; this is the Cheeger--Gromov vanishing from a normal subgroup, which that criterion consumes for the stabilizers.
---

**ESTABLISHED (literature import).** If a group `G` contains an infinite amenable normal subgroup,
then `β_n^(2)(G) = 0` for every `n >= 0`.

No countability is assumed. The survey's Theorem 6.4(i)--(ii) has no countability hypothesis, as
checked by `ex-verify-backlog` (2026-09-13). The frame criterion applies this to stabilizers of
`GL_r(A)` over uncountable rings.

Originally Cheeger--Gromov (Topology 25, 1986). Route: `l2-betti-infinite-normal-amenable-citation`.
