---
rg: 2
id: thompson-f-two-transitive-actions-satisfy-grid-condition
kind: claim
title: In any 2-transitive action of F, the orbits of the left and right stabilizer parts of a point of (0,1) meet in at most one point
distinct_from:
  thompson-f-transitivity-degree-at-most-two: that claim imports the general two-case proposition and the degree bound for groups of line homeomorphisms; this claim rules out the regular case for F, leaving the grid condition as a necessary condition on every 2-transitive F-action
---

Let `F` act 2-transitively on `Ω`, `|Ω| ≥ 3`. For `x ∈ (0,1)`, let `F_x^-` and
`F_x^+` be the elements of `F` supported in `[0,x]` and in `[x,1]`. They
commute, and `F_x = F_x^- × F_x^+`. Then:

1. `[F,F]` is not regular on `Ω`;
2. every `F_x^-`-orbit and every `F_x^+`-orbit in `Ω` meet in at most one point;
3. consequently, for every `ω ∈ Ω` the map `(aω, bω) ↦ abω` is a bijection from
   `F_x^-ω × F_x^+ω` onto the `F_x`-orbit of `ω` (a grid).

**Proof:** `thompson-f-two-transitive-actions-satisfy-grid-condition-proof`.
