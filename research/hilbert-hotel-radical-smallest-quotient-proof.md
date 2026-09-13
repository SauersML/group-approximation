---
rg: 2
id: hilbert-hotel-radical-smallest-quotient-proof
kind: route
title: Minimality of the Hilbert-hotel radical by transfinite induction
target: hilbert-hotel-radical-is-smallest-directly-finite-quotient
requires: []
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

Full derivation in artifact section 1.

**(1)** At the stable stage `d(R/hh(R)) = 0`, so every one-sided pair of `R/hh(R)` has zero
defect, which is direct finiteness. If `R` is directly finite then `d(R) = 0` and the chain never
leaves `0`.

**(2)** Transfinite induction. `hh_0 = 0 <= I`. Suppose `hh_a <= I`. A one-sided pair of
`R/hh_a` maps to a one-sided pair of `R/I`, whose defect vanishes because `R/I` is directly
finite; so every generator of `d(R/hh_a)` lies in `I/hh_a`, giving `hh_(a+1) <= I`. Unions at
limits.

**(3)** `R/f^(-1)(hh(R')) = R'/hh(R')` is directly finite, so (2) applied to `R` gives
`hh(R) <= f^(-1)(hh(R'))`.

**(4)** Immediate from (2), since the zero ring is directly finite.

**(5)** The argument of (2) verbatim with defects of `M_m(R/hh_a)`, using that the ideals of
`M_m(R)` are the `M_m(I)` and `M_m(R)/M_m(I) = M_m(R/I)`.
