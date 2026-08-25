---
rg: 2
id: one-column-orbit-chromatic-firewall-proof
kind: route
title: Normalize a high-degree column and apply centralizer-area properness
target: one-column-orbit-bounded-area-codes-have-bounded-chromatic-number
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Fix a vertex `v`.  Conjugating each edge filling by `b_v^(-1)` leaves its
number of relator cells unchanged.  Replacing `b_v^(-1)h_vb_v` by `beta` in
the two occurrences inside the commutator costs at most `2B`, so every
normalized neighbor in `(OCF3)` commutes with `beta` through a filling of
area at most `A+2B`.

Centralizer-area properness makes the set of `<beta>`-cosets with such a
representative finite.  Distinctness in `(OCF3)` bounds the out-degree of
`v` uniformly by `D`.  Every induced subgraph inherits this orientation and
has at most `D` times its number of vertices many edges.  Its average degree
is at most `2D`, so it contains a vertex of degree at most `2D`.  Greedy
deletion and reinsertion therefore gives a `(2D+1)`-coloring.  This proves
the claim.
