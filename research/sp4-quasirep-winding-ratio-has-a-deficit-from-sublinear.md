---
rg: 2
id: sp4-quasirep-winding-ratio-has-a-deficit-from-sublinear
kind: route
title: A zero winding ratio is below every positive threshold
target: sp4-quasirep-winding-ratio-has-a-deficit
requires:
  - sp4-quasirep-windings-are-sublinear
  - sp4-winding-ratio-sharp-constant-is-gromov-dual
---

Let `r` and `W` be as in `sp4-quasirep-windings-are-sublinear`, so that `S_W(eps) = o(eps)` and `Theta(W) = 0`.

By item 4 of `sp4-winding-ratio-sharp-constant-is-gromov-dual`:
- `beta*_W` is positive;
- `beta*_W` is at most `|k|/nu < infinity`.

So `|k|/(2 pi beta*_W) > 0 = Theta(W)`.
