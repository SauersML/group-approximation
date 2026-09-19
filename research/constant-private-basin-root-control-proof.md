---
rg: 2
id: constant-private-basin-root-control-proof
kind: route
title: Telescope from each private root to its fixed basin anchor
target: constant-size-private-basins-give-uniform-root-control
requires: []
---

Choose one shortest path of length `ell=dist_H(rho,a)` from `rho` to `a`.
For every `t`, telescoping along the path and Cauchy--Schwarz give

```text
||U_(t,rho)-U_(t,a)||_2^2
 <= ell sum_(uv on path)||U_(t,u)-U_(t,v)||_2^2
 <= ell sum_(uv in E(H))||U_(t,u)-U_(t,v)||_2^2.
```

Average over `t` and multiply/divide by `|E(H)|` to obtain `(CPB1)`.
All copies are disjoint and have the same fixed size, so the degree and
density assertions are immediate.  Adding one cross edge between the two
roots for each `t` leaves mixed degree one.  The basin operation itself adds
no second mixed edge; it makes no claim about contours closed through
relations subsequently added between distinct anchors.
