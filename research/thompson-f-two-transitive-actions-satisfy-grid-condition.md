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
commute and generate `F_x^- × F_x^+ ≤ F_x`. Equality holds when `x` is dyadic
or irrational. It can fail at non-dyadic rational `x`: there an element of
`F_x` may have a nontrivial germ, and cutting it at `x` leaves `F`. Then:

1. `[F,F]` is not regular on `Ω`;
2. every `F_x^-`-orbit and every `F_x^+`-orbit in `Ω` meet in at most one point;
3. for every `ω ∈ Ω`, the map `(aω, bω) ↦ abω` is a bijection from
   `F_x^-ω × F_x^+ω` onto the `(F_x^- × F_x^+)`-orbit of `ω` (a grid);
4. (splitting) for every `ω`, `F_ω ∩ (F_x^- × F_x^+) = (F_ω ∩ F_x^-) × (F_ω ∩ F_x^+)`.
   So if `h ∈ F_ω` fixes a dyadic or irrational `x` (or is the identity near
   `x`), both pieces of `h` cut at `x` lie in `F_ω`.

(Corrected 2026-09-13: the first landing wrote `F_x = F_x^- × F_x^+` for all
`x`, which is false at non-dyadic rationals; items 3 and 4 are stated for the
product subgroup.)

**Proof:** `thompson-f-two-transitive-actions-satisfy-grid-condition-proof`.
