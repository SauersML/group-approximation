---
rg: 2
id: strong-word-graphs-give-short-primitive-periodic-models
kind: claim
title: Strongly connected word graphs give primitive periodic models of complexity-bounded length and characterize unbounded-period limits
artifacts:
  - research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md
---

Let `X` be a nonempty binary subshift and `p_X(r)=|L_r(X)|`. If the
directed prefix-suffix graph with vertices `L_r(X)` and edges
`L_(r+1)(X)` is strongly connected, there is a primitive cyclic binary
word `z` with `L_(r+1)(z^infinity)=L_(r+1)(X)` and
`E<=|z|<=E+(E-V)(V-1)<=VE`, where `V=p_X(r)` and `E=p_X(r+1)`.
For Sturmian complexity `p_X(r)=r+1`, the period bound is `2r+2`.

The subshift limits of primitive periodic orbits with least periods
tending to infinity are exactly the infinite subshifts for which all
these graphs are strongly connected. Every infinite minimal subshift
has this property. For every infinite subshift with this property,
`p_X(r)>=r+1` for all `r>=1`.
