---
rg: 2
id: nonsofic-hyperbolic-group-via-hyperlinear-burnside-finiteness
kind: route
title: If hyperlinear bounded-exponent groups are finite, a Delzant--Gromov stage of a free Burnside group is non-hyperlinear, hence nonsofic
target: nonsofic-hyperbolic-group
requires:
  - hyperlinear-fg-bounded-exponent-groups-are-finite
  - free-burnside-is-a-limit-of-hyperbolic-groups
  - nonsofic-free-burnside-gives-nonsofic-hyperbolic-group
  - sofic-implies-hyperlinear
---

Take `m = 2` and an odd `N >= n_1(F_2)`.

1. `B(2,N)` is infinite by item 4 of
   `free-burnside-is-a-limit-of-hyperbolic-groups`. It is finitely generated,
   and its exponent divides `N`.
   - If it were hyperlinear, `hyperlinear-fg-bounded-exponent-groups-are-finite`
     would make it finite.
   - So `B(2,N)` is non-hyperlinear.
2. Apply `nonsofic-free-burnside-gives-nonsofic-hyperbolic-group` with `P`
   equal to hyperlinearity. It gives a stage `G_k` that is a non-hyperlinear,
   non-elementary hyperbolic group.
3. By `sofic-implies-hyperlinear`, that `G_k` is not sofic.

The route yields more than its target: it gives a non-hyperlinear hyperbolic
group. Its only open requirement is
`hyperlinear-fg-bounded-exponent-groups-are-finite`, the same one carried by
`non-hyperlinear-group-via-hyperlinear-burnside-finiteness`. So that finiteness
claim now bears on the hyperbolic soficity problem too, not only on the
existence of some non-hyperlinear group.
