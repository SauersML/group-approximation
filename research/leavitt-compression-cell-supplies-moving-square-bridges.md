---
rg: 2
id: leavitt-compression-cell-supplies-moving-square-bridges
kind: route
title: Use the canonical Leavitt compression cell as the six moving bridges
target: el20-six-moving-coefficient-square-bridges
requires:
  - leavitt-whitehead-20x20-compression-cell
---

**INVALIDATED CANONICAL-COMPRESSION ROUTE.** Use the explicit
Whitehead/Hilbert-hotel cell implementing
`r |-> p_1+s_0rt_0` as one ungauged full-Leavitt bridge, and use its six
Singer conjugates for the moving square table.

`leavitt-compression-preserves-root-position-support` invalidates this
route. Compression preserves every ordered elementary-root position,
whereas the Singer step carries an actual `(2,8)` root in the signed Hecke
subgroup to `(2,7)`. Accordingly the cell sends the source Reynolds cut to
the Reynolds cut over `alpha(L_0)`, not to the next Singer cut over
`tL_0t^(-1)`. The candidate fails the full-Gram requirement before any
mixed-square or error estimate is considered.

