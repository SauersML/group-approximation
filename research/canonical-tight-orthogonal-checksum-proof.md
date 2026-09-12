---
rg: 2
id: canonical-tight-orthogonal-checksum-proof
kind: route
title: Take the matrix limit before the orthogonal tail limit
target: canonical-tight-orthogonal-checksum-collapses-one-mark
requires:
  - depthwise-canonical-kleene-needs-no-uniform-runtime-gap
  - orthogonal-checksum-controls-only-mass-weighted-syndromes
---

Fix `N`.  Since the initial projections in `(CTO1)` and `T_(m,N)` are
orthogonal, tracial cyclicity gives the exact Pythagorean identity

```text
 ||(W_m-I)P_m||_2^2
 =sum_(n<=N)||(W_m-I)P_(m,n)||_2^2
  +||(W_m-I)T_(m,N)||_2^2.                              (CTP1)
```

The last term is at most `4 tr_m(T_(m,N))`, since `W_m` is unitary.  First
let `m->infinity` with `N` fixed.  Every one of the finitely many block
terms vanishes by `(CTO2)`, regardless of its finite proof constant, while
the tail is at most `4b_N`.  Thus

```text
 limsup_m||(W_m-I)P_m||_2^2<=4b_N.                      (CTP2)
```

Only now let `N->infinity`.  This proves `(CTO4)` and is exactly the
depthwise-canonical order of limits.

For the dilution fence, take a direct sum whose carrier mass is concentrated
on one decoded block type `k_m->infinity`.  Every fixed `P_(m,n)` then has
trace tending to zero, while the tail in `(CTO1)` retains the full carrier
mass for all fixed `N`.  Hence `(CTO3)` fails.  Orthogonality did not stop
the escape; tight canonical trace data did.

