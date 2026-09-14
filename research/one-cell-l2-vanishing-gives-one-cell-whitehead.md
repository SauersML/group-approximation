---
rg: 2
id: one-cell-l2-vanishing-gives-one-cell-whitehead
kind: route
title: Vanishing first L²-Betti numbers of one-cell complement groups give Whitehead's finite one-cell case
target: contractible-2-complex-minus-a-cell-is-aspherical
requires:
  - one-cell-complement-groups-have-vanishing-first-l2-betti
  - whitehead-one-cell-counterexamples-have-positive-first-l2-betti
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

Let L be a finite connected contractible 2-complex, e an open 2-cell, and K = L − e.
- `one-cell-complement-groups-have-vanishing-first-l2-betti` gives b₁^(2)(π₁K) = 0.
- If K were not aspherical, `whitehead-one-cell-counterexamples-have-positive-first-l2-betti`
  would give b₁^(2)(π₁K) > 0.

So K is aspherical.
